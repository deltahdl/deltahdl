#include <algorithm>
#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
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
  ForEachChildExpr(s,
                   [this](const Expr* e) { WalkExprForTypedArrayPattern(e); });
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForProceduralArrayPattern(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

const ModuleItem* ElaboratorOperationRules::TypeRefVariable(
    const Expr* ref) const {
  std::string_view name = ExprIdent(ref->lhs);
  if (IsBlockDeclared(block_decls_, name)) return nullptr;
  auto it = pattern_target_arrays_.find(name);
  return it == pattern_target_arrays_.end() ? nullptr : it->second;
}

// §10.9: a pattern prefixed with a type parses as a cast wrapping it, and the
// type the prefix names is the one its braces follow (§10.9.1). A typedef's
// name is the element type its entry holds, with the unpacked dimensions an
// array typedef carries kept apart (§7.4.4); a name no typedef in scope gives,
// an integer atom type among them, has no dimensions to count against.
// `type(...)` encloses either a data type or an expression, whose type §6.23
// makes the reference's.
void ElaboratorOperationRules::CheckTypedArrayPattern(const Expr* e) {
  if (e->kind != ExprKind::kCast ||
      e->lhs->kind != ExprKind::kAssignmentPattern)
    return;
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  const Expr* ref = e->rhs;
  if (ref == nullptr) {
    auto td = typedefs_.find(e->text);
    if (td == typedefs_.end()) return;
    std::vector<Expr*> unpacked_dims;
    auto dims = td_array_dims_.find(e->text);
    if (dims != td_array_dims_.end()) unpacked_dims = dims->second;
    kCheck.Check(e->lhs, td->second, unpacked_dims, e->range.start);
    return;
  }
  if (ref->type_value != nullptr) {
    kCheck.Check(e->lhs, *ref->type_value, {}, e->range.start);
    return;
  }
  if (const ModuleItem* var = TypeRefVariable(ref))
    kCheck.Check(e->lhs, var->data_type, var->unpacked_dims, e->range.start);
}

void ElaboratorOperationRules::WalkExprForTypedArrayPattern(const Expr* e) {
  if (e == nullptr) return;
  CheckTypedArrayPattern(e);
  ForEachExprChild(
      e, [this](const Expr* child) { WalkExprForTypedArrayPattern(child); });
}

// A module item's own expressions: a declaration's initializer, both sides of
// a continuous assignment, and an instance's port connections.
void ElaboratorOperationRules::WalkItemForTypedArrayPatterns(
    const ModuleItem* item) {
  WalkExprForTypedArrayPattern(item->init_expr);
  WalkExprForTypedArrayPattern(item->assign_lhs);
  WalkExprForTypedArrayPattern(item->assign_rhs);
  for (const auto& conn : item->inst_ports)
    WalkExprForTypedArrayPattern(conn.second);
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

// §10.8 counts a continuous assignment and a net declaration assignment among
// the assignment-like contexts, so §10.9.1 holds the pattern each drives to the
// dimensions of its target: the variable or net its left-hand side names
// whole, or the net it declares.
void ElaboratorOperationRules::CheckContinuousArrayPattern(
    const ModuleItem* item) {
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  if (item->kind == ModuleItemKind::kNetDecl && item->init_expr != nullptr) {
    kCheck.Check(item->init_expr, item->data_type, item->unpacked_dims,
                 item->init_expr->range.start);
  }
  if (item->kind != ModuleItemKind::kContAssign ||
      item->assign_lhs->kind != ExprKind::kIdentifier)
    return;
  auto it = pattern_target_arrays_.find(item->assign_lhs->text);
  if (it == pattern_target_arrays_.end()) return;
  kCheck.Check(item->assign_rhs, it->second->data_type,
               it->second->unpacked_dims, item->assign_rhs->range.start);
}

// A subroutine's formals hide the module's declarations of their names in its
// body as a block's declarations do.
void ElaboratorOperationRules::ValidateProceduralArrayPatterns(
    const ModuleDecl* decl) {
  pattern_target_arrays_.clear();
  StructTargetTypes struct_targets;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNetDecl)
      pattern_target_arrays_[item->name] = item;
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    pattern_target_arrays_[item->name] = item;
    if (item->unpacked_dims.empty())
      struct_targets[item->name] = &item->data_type;
  }
  for (const auto& param : decl->params)
    WalkExprForTypedArrayPattern(param.second);
  for (const auto* item : decl->items) {
    CheckContinuousArrayPattern(item);
    WalkItemForTypedArrayPatterns(item);
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
