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

std::string BlockEnumKey(const ModuleItem* td, std::string_view path) {
  return std::format("$block::{}{}{}@{:x}", td->name, path.empty() ? "" : ".",
                     path, reinterpret_cast<std::uintptr_t>(td));
}

std::string BlockVarEnumKey(const Stmt* s) {
  return std::format("$block::@{:x}", reinterpret_cast<std::uintptr_t>(s));
}

const ModuleItem* BlockTypedefOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kBlockItemDecl) return nullptr;
  const ModuleItem* td = s->decl_item;
  if (td == nullptr || td->kind != ModuleItemKind::kTypedef) return nullptr;
  return td;
}

const ModuleItem* BlockTypeParamOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kVarDecl || !s->var_is_param)
    return nullptr;
  const ModuleItem* param = s->decl_item;
  if (param->data_type.kind != DataTypeKind::kVoid) return nullptr;
  return param;
}

struct BlockTypeName {
  std::string_view key;
  const DataType* type = nullptr;
};

using BlockTypeNames = std::unordered_map<std::string_view, BlockTypeName>;

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

  void RegisterTypedef(const ModuleItem* td, BlockTypeNames& aliases) {
    ForEachEnumTypeOfItem(td, [&](std::string_view path, const DataType& t) {
      auto* key = arena.Create<std::string>(BlockEnumKey(td, path));
      if (ctx.FindEnumType(*key) == nullptr) Register(*key, t);
      if (!path.empty()) return;
      aliases[td->name] = {*key};
      ctx.RegisterTypeDeclaration(*key, td);
    });
  }

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

  void Register(std::string_view key, const DataType& type) {
    EnumTypeInfo info;
    info.type_name = key;
    info.width = EvalTypeWidth(EnumArrayElement(type));
    info.is_4state = Is4stateType(type, TypedefMap{});
    info.is_signed = IsSignedType(type, TypedefMap{});
    for (const RtlirEnumMember& m :
         FoldEnumMembers(type.enum_members, scope, arena)) {
      info.members.push_back(EnumMemberInfoOf(m, info.width, ctx, arena));
    }
    ctx.RegisterEnumType(key, info);
    ctx.RegisterTypeWidth(key, EvalTypeWidth(type));
    ctx.RegisterTypeKind(key, DataTypeKind::kEnum);
    ctx.RegisterTypeSigned(key, IsSignedType(type, TypedefMap{}));
  }

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

  void ReshapeDecl(const Stmt* s, const BlockTypeNames& aliases) {
    const DataType& type = s->var_decl_type;
    if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) return;
    auto it = aliases.find(type.type_name);
    if (it == aliases.end()) return;
    auto* shaped = arena.Create<Stmt>(*s);
    shaped->var_decl_type = TypeThroughName(type, it->second);
    ctx.ClassTypedefShapedDecls()[s] = shaped;
  }

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
