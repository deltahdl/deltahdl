#include "simulator/block_enums.h"

#include <cstdint>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {
namespace {

// The key an enumeration a block's typedef `td` declares is registered under:
// the typedef's name, the member path of one written as a structure or union
// member's type, and the declaration's address, which no other typedef
// shares. The `$block::` scope is spelled by no source name, and puts the key
// among the scoped ones SimContext::FindEnumTypeDeclaringMember falls back to
// only where no enumeration of the module declares the member.
std::string BlockEnumKey(const ModuleItem* td, std::string_view path) {
  return std::format("$block::{}{}{}@{:x}", td->name, path.empty() ? "" : ".",
                     path, reinterpret_cast<std::uintptr_t>(td));
}

// The key the inline enumeration of a block variable's declaration `s`,
// `enum {r, s} y;`, is registered under: the declaration's address, which no
// other declaration shares, in the `$block::` scope BlockEnumKey's are.
std::string BlockVarEnumKey(const Stmt* s) {
  return std::format("$block::@{:x}", reinterpret_cast<std::uintptr_t>(s));
}

// The typedef a block item declaration `s` declares, or null.
const ModuleItem* BlockTypedefOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kBlockItemDecl) return nullptr;
  const ModuleItem* td = s->decl_item;
  if (td == nullptr || td->kind != ModuleItemKind::kTypedef) return nullptr;
  return td;
}

// The type parameter a block item declaration `s` declares, or null. The
// parser carries a block's parameter as a kVarDecl over the item it read
// (Parser::ParseBlockVarDecls), and a type parameter's item holds its type in
// typedef_type with a void data_type, as Elaborator::ElaborateParamDecl tells
// one at module scope.
const ModuleItem* BlockTypeParamOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kVarDecl || !s->var_is_param)
    return nullptr;
  const ModuleItem* param = s->decl_item;
  if (param->data_type.kind != DataTypeKind::kVoid) return nullptr;
  return param;
}

// What a type name a block has declared stands for: the key its enumeration,
// structure or union is registered under, or, for any other type, the type.
struct BlockTypeName {
  std::string_view key;
  const DataType* type = nullptr;
};

// The type names a block has declared by the statement being walked.
using BlockTypeNames = std::unordered_map<std::string_view, BlockTypeName>;

// §7.4.4: the type `named` stands for, as a declaration that names it with
// the type `use` has it. Packed dimensions written where the name is used
// stack outside the type's own, so `T [1:0] w` on a `logic [7:0]` T is a
// `logic [1:0][7:0]`.
DataType StackedOnNamedType(const DataType& use, const DataType& named) {
  DataType out = named;
  out.is_const = use.is_const;
  if (use.packed_dim_left == nullptr) return out;
  std::vector<std::pair<Expr*, Expr*>> inner = use.extra_packed_dims;
  if (named.packed_dim_left != nullptr)
    inner.emplace_back(named.packed_dim_left, named.packed_dim_right);
  inner.insert(inner.end(), named.extra_packed_dims.begin(),
               named.extra_packed_dims.end());
  out.packed_dim_left = use.packed_dim_left;
  out.packed_dim_right = use.packed_dim_right;
  out.extra_packed_dims = std::move(inner);
  return out;
}

// §6.18: the type a declaration written with the type `use` has, where `use`
// names a block type name that stands for `name`: the key its enumeration,
// structure or union is registered under, packed dimensions and all, or the
// plain type with `use`'s packed dimensions stacked on it.
DataType TypeThroughName(const DataType& use, const BlockTypeName& name) {
  if (name.type != nullptr) return StackedOnNamedType(use, *name.type);
  DataType out = use;
  out.type_name = name.key;
  return out;
}

struct BlockEnumWalk {
  const ScopeMap& scope;
  SimContext& ctx;
  Arena& arena;

  // Registers the enumerations the typedef `td` declares, and makes its name
  // stand for the one it declares at the top, if any, in `aliases`. §7.4.1
  // with §7.4.4: that one is recorded as the declaration behind its key
  // (SimContext::RegisterTypeDeclaration), where RecordPackedRange reads the
  // dimensions after its body that make a variable of it an array of the
  // enumeration, so `x[1]` selects one element.
  void RegisterTypedef(const ModuleItem* td, BlockTypeNames& aliases) {
    ForEachEnumTypeOfItem(td, [&](std::string_view path, const DataType& t) {
      auto* key = arena.Create<std::string>(BlockEnumKey(td, path));
      if (ctx.FindEnumType(*key) == nullptr) Register(*key, t);
      if (!path.empty()) return;
      aliases[td->name] = {*key};
      ctx.RegisterTypeDeclaration(*key, td);
    });
  }

  // §6.18 with §7.2 and §7.3: a structure or union the typedef `td`
  // declares at its top is registered as a layout under the typedef's key,
  // with the width, kind and signedness a declaration by that key reads, and
  // its name is made to stand for that key in `aliases`, so a variable the
  // block declares by the name is an object of the layout and a member write
  // lands in its window. With no layout, `p.a = 3` wrote nothing and `p.a`
  // read 0.
  void RegisterAggregateTypedef(const ModuleItem* td, BlockTypeNames& aliases) {
    const DataType& type = td->typedef_type;
    if ((type.kind != DataTypeKind::kStruct &&
         type.kind != DataTypeKind::kUnion) ||
        !td->unpacked_dims.empty()) {
      return;
    }
    auto* key = arena.Create<std::string>(BlockEnumKey(td, {}));
    if (ctx.FindStructType(*key) == nullptr) {
      RegisterTypeLayout(*key, &type, ctx, arena);
      const StructTypeInfo* info = ctx.FindStructType(*key);
      if (info == nullptr) return;
      ctx.RegisterTypeWidth(*key, info->total_width);
      ctx.RegisterTypeKind(*key, type.kind);
      ctx.RegisterTypeSigned(*key, IsSignedType(type, TypedefMap{}));
    }
    aliases[td->name] = {*key};
  }

  // §6.18 and §6.20.3: a typedef or type parameter `item` of the block whose
  // type registers no enumeration, structure or union key -- a vector, an
  // integer or real type, a string, a class -- makes its name stand for that
  // type, so a declaration the block writes by the name is one of the type
  // written out (ReshapeDecl). A type that is itself one of the block's type
  // names, written with no scope, is the type that name stands for.
  void RegisterPlainType(const ModuleItem* item, BlockTypeNames& aliases) {
    const DataType& type = item->typedef_type;
    auto named = type.kind == DataTypeKind::kNamed && type.scope_name.empty()
                     ? aliases.find(type.type_name)
                     : aliases.end();
    const DataType* stands_for =
        named == aliases.end()
            ? &type
            : arena.Create<DataType>(TypeThroughName(type, named->second));
    aliases[item->name] = {{}, stands_for};
  }

  // §6.19 with §7.4.1: the members are as wide as the enumeration alone,
  // and a declaration by the key is as wide as the packed array of it the
  // dimensions after its body make.
  void Register(std::string_view key, const DataType& type) {
    EnumTypeInfo info;
    info.type_name = key;
    info.width = EvalTypeWidth(EnumArrayElement(type));
    info.is_4state = Is4stateType(type, TypedefMap{});
    for (const RtlirEnumMember& m :
         FoldEnumMembers(type.enum_members, scope, arena)) {
      info.members.push_back(EnumMemberInfoOf(m, info.width, ctx, arena));
    }
    ctx.RegisterEnumType(key, info);
    ctx.RegisterTypeWidth(key, EvalTypeWidth(type));
    ctx.RegisterTypeKind(key, DataTypeKind::kEnum);
    ctx.RegisterTypeSigned(key, IsSignedType(type, TypedefMap{}));
  }

  // §6.19 with A.2.8: a block variable declared with an inline enumerated
  // type is of that enumeration, which is registered under the declaration's
  // own key and named by a reshaped copy of the declaration, as a typedef's
  // is. The key's width already holds the base type's range and the packed
  // dimensions after the body (§7.4.1), so the copy names the key with none
  // of its own: one left on it is a use-site dimension stacking on the key's
  // width (§7.4.4), and `enum logic [2:0] {P, Q} [1:0] w` was 18 bits. The
  // dimensions are read instead off a typedef of the enumeration recorded as
  // the declaration behind the key, as RegisterTypedef records a block
  // typedef's, so `w[1]` selects one element.
  void RegisterInlineEnum(const Stmt* s) {
    auto* key = arena.Create<std::string>(BlockVarEnumKey(s));
    if (ctx.FindEnumType(*key) == nullptr) {
      Register(*key, s->var_decl_type);
      auto* item = arena.Create<ModuleItem>();
      item->kind = ModuleItemKind::kTypedef;
      item->name = *key;
      item->typedef_type = s->var_decl_type;
      ctx.RegisterTypeDeclaration(*key, item);
    }
    auto* shaped = arena.Create<Stmt>(*s);
    shaped->var_decl_type.kind = DataTypeKind::kNamed;
    shaped->var_decl_type.type_name = *key;
    shaped->var_decl_type.enum_members.clear();
    shaped->var_decl_type.packed_dim_left = nullptr;
    shaped->var_decl_type.packed_dim_right = nullptr;
    shaped->var_decl_type.extra_packed_dims.clear();
    shaped->var_decl_type.enum_array_dims.clear();
    ctx.ClassTypedefShapedDecls()[s] = shaped;
  }

  // §6.18: a declaration naming a typedef or type parameter of the block is
  // of the type the name stands for, so it is reshaped to name the key that
  // type is registered under, or to be of the type itself.
  void ReshapeDecl(const Stmt* s, const BlockTypeNames& aliases) {
    const DataType& type = s->var_decl_type;
    if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) return;
    auto it = aliases.find(type.type_name);
    if (it == aliases.end()) return;
    auto* shaped = arena.Create<Stmt>(*s);
    shaped->var_decl_type = TypeThroughName(type, it->second);
    ctx.ClassTypedefShapedDecls()[s] = shaped;
  }

  // A statement list whose typedefs and type parameters are visible to the
  // statements after them and to everything those hold (§23.9), a begin-end
  // or fork-join block's or a subroutine body's. A typedef hides whatever its
  // name stood for in an enclosing block. One with an unpacked dimension
  // stands for no plain type, its dimensions being the declaration's to
  // adopt (§7.4.4).
  template <typename List>
  void WalkList(const List& stmts, BlockTypeNames aliases) {
    for (const Stmt* s : stmts) {
      if (const ModuleItem* td = BlockTypedefOf(s)) {
        aliases.erase(td->name);
        RegisterTypedef(td, aliases);
        RegisterAggregateTypedef(td, aliases);
        if (!aliases.contains(td->name) && td->unpacked_dims.empty())
          RegisterPlainType(td, aliases);
        continue;
      }
      if (const ModuleItem* param = BlockTypeParamOf(s)) {
        RegisterPlainType(param, aliases);
        continue;
      }
      Walk(s, aliases);
    }
  }

  void Walk(const Stmt* s, const BlockTypeNames& aliases) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kVarDecl &&
        s->var_decl_type.kind == DataTypeKind::kEnum) {
      RegisterInlineEnum(s);
    } else if (s->kind == StmtKind::kVarDecl) {
      ReshapeDecl(s, aliases);
    }
    if (s->kind == StmtKind::kBlock) return WalkList(s->stmts, aliases);
    if (s->kind == StmtKind::kFork) return WalkList(s->fork_stmts, aliases);
    ForEachChildStmt(s, [&](Stmt* const& sub) { Walk(sub, aliases); });
  }
};

// The constants a block's enumeration member value may name: the compilation
// unit's, the module's parameters and the members of its enumerations.
ScopeMap BlockEnumScope(const RtlirModule* mod, const RtlirDesign* design) {
  ScopeMap scope;
  if (design != nullptr) scope = design->unit_constants;
  for (const auto& p : mod->params) {
    if (p.gen_block_prefix.empty()) scope[p.name] = p.resolved_value;
  }
  for (const auto& [name, members] : mod->enum_types) {
    for (const auto& m : members) scope[m.name] = m.value;
  }
  return scope;
}

}  // namespace

void RegisterBlockEnumTypes(const RtlirModule* mod, const RtlirDesign* design,
                            SimContext& ctx, Arena& arena) {
  ScopeMap scope = BlockEnumScope(mod, design);
  BlockEnumWalk walk{scope, ctx, arena};
  for (const auto& proc : mod->processes) walk.Walk(proc.body, {});
  for (const ModuleItem* func : mod->function_decls) {
    walk.WalkList(func->func_body_stmts, {});
  }
  // §8.3: a class's methods are subroutines whose bodies are blocks too, of
  // a class the module declares or of the compilation unit's.
  auto walk_methods = [&](const ClassDecl* cls) {
    for (const ClassMember* m : cls->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method != nullptr)
        walk.WalkList(m->method->func_body_stmts, {});
    }
  };
  for (const ClassDecl* cls : mod->class_decls) walk_methods(cls);
  if (design == nullptr) return;
  for (const ClassDecl* cls : design->cu_class_decls) walk_methods(cls);
}

void ForEachBlockEnumMember(
    const Stmt* stmt, SimContext& ctx,
    const std::function<void(const EnumMemberInfo&, const EnumTypeInfo&)>& fn) {
  if (stmt != nullptr && stmt->kind == StmtKind::kVarDecl &&
      stmt->var_decl_type.kind == DataTypeKind::kEnum) {
    const EnumTypeInfo* info = ctx.FindEnumType(BlockVarEnumKey(stmt));
    if (info == nullptr) return;
    for (const EnumMemberInfo& m : info->members) fn(m, *info);
    return;
  }
  const ModuleItem* td = BlockTypedefOf(stmt);
  if (td == nullptr) return;
  ForEachEnumTypeOfItem(td, [&](std::string_view path, const DataType&) {
    const EnumTypeInfo* info = ctx.FindEnumType(BlockEnumKey(td, path));
    if (info == nullptr) return;
    for (const EnumMemberInfo& m : info->members) fn(m, *info);
  });
}

}  // namespace delta
