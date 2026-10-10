#include <algorithm>
#include <cstddef>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// Whether a block the walk is inside declares `name`, which hides the module's
// declaration of it for the rest of that block (§6.21, §23.9).
static bool IsBlockDeclared(
    const std::vector<std::pair<std::string_view, bool>>& decls,
    std::string_view name) {
  return std::ranges::any_of(
      decls, [name](const auto& decl) { return decl.first == name; });
}

// §5.10 with §5.11 and §10.9.1 holds a pattern to its array wherever it is
// written: assigned by a procedure to the module's array, `abarr = '{...}`, or
// initializing an array a block declares. Only the module-level declaration's
// initializer was checked, so a flat pattern for an array of structures and a
// pattern of the wrong element count went through in both places.
void ElaboratorOperationRules::WalkStmtsForProceduralArrayPattern(
    const Stmt* s) {
  if (s == nullptr) return;
  const ArrayPatternCheck kCheck{typedefs_, var_types_, diag_};
  bool is_assign = s->kind == StmtKind::kBlockingAssign ||
                   s->kind == StmtKind::kNonblockingAssign;
  if (is_assign && s->lhs->kind == ExprKind::kIdentifier &&
      !IsBlockDeclared(block_decls_, s->lhs->text)) {
    auto it = pattern_target_arrays_.find(s->lhs->text);
    if (it != pattern_target_arrays_.end()) {
      kCheck.Check(s->rhs, it->second->data_type, it->second->unpacked_dims,
                   s->rhs->range.start);
    }
  }
  if (s->kind == StmtKind::kVarDecl && s->var_init != nullptr &&
      !s->var_unpacked_dims.empty()) {
    kCheck.Check(s->var_init, s->var_decl_type, s->var_unpacked_dims,
                 s->var_init->range.start);
  }
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForProceduralArrayPattern(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

// A subroutine's formals hide the module's declarations of their names in its
// body as a block's declarations do.
void ElaboratorOperationRules::ValidateProceduralArrayPatterns(
    const ModuleDecl* decl) {
  pattern_target_arrays_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->unpacked_dims.empty())
      pattern_target_arrays_[item->name] = item;
  }
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForProceduralArrayPattern(item->body);
    for (const auto& arg : item->func_args)
      block_decls_.emplace_back(arg.name, !arg.unpacked_dims.empty());
    for (const auto* s : item->func_body_stmts)
      WalkStmtsForProceduralArrayPattern(s);
    block_decls_.clear();
  }
}

}  // namespace delta
