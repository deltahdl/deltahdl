#include <algorithm>
#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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
// initializing an array a block declares, a packed array (§7.4) among them.
// Only the module-level declaration's initializer was checked, so a flat
// pattern for an array of structures and a pattern of the wrong element count
// went through in both places.
void ElaboratorOperationRules::WalkStmtsForProceduralArrayPattern(
    const Stmt* s) {
  if (s == nullptr) return;
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
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
  if (s->kind == StmtKind::kVarDecl && s->var_init != nullptr) {
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

using StructTargetTypes = std::unordered_map<std::string_view, const DataType*>;

// The type a procedural assignment's target is declared with where the target
// names a whole variable that is no array: a name the body declares, which
// hides the module's, or a module variable of `module_types`.
static const DataType* WholeTargetType(const Expr* lhs,
                                       const BodyDeclScopes& scopes,
                                       const StructTargetTypes& module_types) {
  if (lhs->kind != ExprKind::kIdentifier) return nullptr;
  if (const BodyDeclScopes::Decl* decl = scopes.Find(lhs->text))
    return decl->unpacked_dims->empty() ? decl->type : nullptr;
  auto it = module_types.find(lhs->text);
  return it == module_types.end() ? nullptr : it->second;
}

// §10.9.2 (printed pages 263-264) holds a structure pattern to its structure
// wherever it is written -- a typed pattern to the type its prefix names, and
// an untyped one to the variable it is assigned to or initializes -- and not
// only where a module-level declaration is initialized.
static void CheckProceduralStructPatterns(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const StructTargetTypes& module_types, const TypedefMap& typedefs,
    DiagEngine& diag) {
  BodyDeclScopes scopes(false);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (st->kind == StmtKind::kVarDecl && st->var_init != nullptr &&
          st->var_unpacked_dims.empty()) {
        CheckStructPatternFor(st->var_init, &st->var_decl_type,
                              {typedefs, st->var_init->range.start, diag});
      }
      if (st->kind != StmtKind::kBlockingAssign &&
          st->kind != StmtKind::kNonblockingAssign)
        return;
      CheckStructPatternFor(st->rhs,
                            WholeTargetType(st->lhs, scopes, module_types),
                            {typedefs, st->rhs->range.start, diag});
    });
  }
}

// The structure patterns one item writes: in a process's or a subroutine's
// statements, and on the right of a continuous assignment, whose target no
// block declaration hides.
static void CheckItemStructPatterns(const ModuleItem* item,
                                    const StructTargetTypes& targets,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  if (IsProceduralItemKind(item->kind))
    CheckProceduralStructPatterns({}, {item->body}, targets, typedefs, diag);
  CheckProceduralStructPatterns(item->func_args, item->func_body_stmts, targets,
                                typedefs, diag);
  if (item->kind != ModuleItemKind::kContAssign) return;
  const BodyDeclScopes kNoLocals(false);
  CheckStructPatternFor(item->assign_rhs,
                        WholeTargetType(item->assign_lhs, kNoLocals, targets),
                        {typedefs, item->assign_rhs->range.start, diag});
}

// A subroutine's formals hide the module's declarations of their names in its
// body as a block's declarations do.
void ElaboratorOperationRules::ValidateProceduralArrayPatterns(
    const ModuleDecl* decl) {
  pattern_target_arrays_.clear();
  StructTargetTypes struct_targets;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    pattern_target_arrays_[item->name] = item;
    if (item->unpacked_dims.empty())
      struct_targets[item->name] = &item->data_type;
  }
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForProceduralArrayPattern(item->body);
    CheckItemStructPatterns(item, struct_targets, typedefs_, diag_);
    for (const auto& arg : item->func_args)
      block_decls_.emplace_back(arg.name, !arg.unpacked_dims.empty());
    for (const auto* s : item->func_body_stmts)
      WalkStmtsForProceduralArrayPattern(s);
    block_decls_.clear();
  }
}

}  // namespace delta
