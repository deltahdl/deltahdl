#include "simulator/block_enums.h"

#include <cstdint>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
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

// The typedef a block item declaration `s` declares, or null.
const ModuleItem* BlockTypedefOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kBlockItemDecl) return nullptr;
  const ModuleItem* td = s->decl_item;
  if (td == nullptr || td->kind != ModuleItemKind::kTypedef) return nullptr;
  return td;
}

// The typedef names a block has declared by the statement being walked, each
// with the key its enumeration is registered under.
using BlockEnumAliases = std::unordered_map<std::string_view, std::string_view>;

struct BlockEnumWalk {
  const ScopeMap& scope;
  SimContext& ctx;
  Arena& arena;

  // Registers the enumerations the typedef `td` declares, and makes its name
  // stand for the one it declares at the top, if any, in `aliases`.
  void RegisterTypedef(const ModuleItem* td, BlockEnumAliases& aliases) {
    ForEachEnumTypeOfItem(td, [&](std::string_view path, const DataType& t) {
      auto* key = arena.Create<std::string>(BlockEnumKey(td, path));
      if (ctx.FindEnumType(*key) == nullptr) Register(*key, t);
      if (path.empty()) aliases[td->name] = *key;
    });
  }

  void Register(std::string_view key, const DataType& type) {
    EnumTypeInfo info;
    info.type_name = key;
    info.width = EvalTypeWidth(type);
    info.is_4state = Is4stateType(type, TypedefMap{});
    for (const RtlirEnumMember& m :
         FoldEnumMembers(type.enum_members, scope, arena)) {
      info.members.push_back(EnumMemberInfoOf(m, info.width, ctx, arena));
    }
    ctx.RegisterEnumType(key, info);
    ctx.RegisterTypeWidth(key, info.width);
    ctx.RegisterTypeKind(key, DataTypeKind::kEnum);
    ctx.RegisterTypeSigned(key, IsSignedType(type, TypedefMap{}));
  }

  // §6.18: a declaration naming a typedef of the block is of the typedef's
  // type, so it is reshaped to name the key that type is registered under.
  void ReshapeDecl(const Stmt* s, const BlockEnumAliases& aliases) {
    const DataType& type = s->var_decl_type;
    if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) return;
    auto it = aliases.find(type.type_name);
    if (it == aliases.end()) return;
    auto* shaped = arena.Create<Stmt>(*s);
    shaped->var_decl_type.type_name = it->second;
    ctx.ClassTypedefShapedDecls()[s] = shaped;
  }

  // A statement list whose typedefs are visible to the statements after them
  // and to everything those hold (§23.9), a begin-end or fork-join block's or
  // a subroutine body's.
  template <typename List>
  void WalkList(const List& stmts, BlockEnumAliases aliases) {
    for (const Stmt* s : stmts) {
      if (const ModuleItem* td = BlockTypedefOf(s)) {
        RegisterTypedef(td, aliases);
        continue;
      }
      Walk(s, aliases);
    }
  }

  void Walk(const Stmt* s, const BlockEnumAliases& aliases) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kVarDecl) ReshapeDecl(s, aliases);
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
}

void ForEachBlockEnumMember(
    const Stmt* stmt, SimContext& ctx,
    const std::function<void(const EnumMemberInfo&, const EnumTypeInfo&)>& fn) {
  const ModuleItem* td = BlockTypedefOf(stmt);
  if (td == nullptr) return;
  ForEachEnumTypeOfItem(td, [&](std::string_view path, const DataType&) {
    const EnumTypeInfo* info = ctx.FindEnumType(BlockEnumKey(td, path));
    if (info == nullptr) return;
    for (const EnumMemberInfo& m : info->members) fn(m, *info);
  });
}

}  // namespace delta
