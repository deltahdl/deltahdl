#include <cstddef>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

// §11.4.12's unsized constants in a concatenation, and the unpacked array
// concatenations of §10.10 they are allowed in, apart from the other array
// rules in elaborator_validate_operations_arrays.cpp for the line limit.

namespace delta {

namespace {
// Flags any unsized integer literal sitting directly inside a concatenation;
// such literals lack a self-determined width and are illegal there.
void CheckConcatElementsForUnsized(const Expr* concat, DiagEngine& diag) {
  for (auto* elem : concat->elements) {
    if (elem->kind == ExprKind::kIntegerLiteral) {
      auto tick = elem->text.find('\'');
      if (tick == std::string_view::npos || tick == 0) {
        diag.Error(elem->range.start,
                   "unsized constant is not allowed in a concatenation",
                   Subclause("11.4.12"));
      }
    }
  }
}
}  // namespace

void ElaboratorOperationRules::WalkExprForUnsizedInConcat(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kConcatenation) {
    CheckConcatElementsForUnsized(expr, diag_);
  }
  WalkExprForUnsizedInConcat(expr->lhs);
  WalkExprForUnsizedInConcat(expr->rhs);
  WalkExprForUnsizedInConcat(expr->condition);
  WalkExprForUnsizedInConcat(expr->true_expr);
  WalkExprForUnsizedInConcat(expr->false_expr);
  for (auto* elem : expr->elements) {
    // §11.4.12.1: the unsized-constant restriction is a packed-concatenation
    // rule. A concatenation that is an item of an assignment pattern '{...} is
    // an unpacked array concatenation (§10.10), where unsized constants are
    // legal, so descend into it without applying the element check to it.
    if (expr->kind == ExprKind::kAssignmentPattern &&
        elem->kind == ExprKind::kConcatenation) {
      for (auto* sub : elem->elements) WalkExprForUnsizedInConcat(sub);
      continue;
    }
    WalkExprForUnsizedInConcat(elem);
  }
  for (auto* arg : expr->args) WalkExprForUnsizedInConcat(arg);
}

// §8.13: a property a base class declares is a property of the derived class,
// so `name` is looked for from `cls` up the chain, the nearest declaration
// winning as ordinary member lookup has it. A parameter is carried as a
// property member too (ClassMember::is_param) and is no property.
static const ClassMember* FindClassProperty(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c != nullptr;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty && !m->is_param &&
          m->name == name) {
        return m;
      }
    }
  }
  return nullptr;
}

// §7.4 with §7.10 (printed pages 153 and 169): whether `sel` selects one
// element of an array `arrays` records as one whose elements are queues, which
// makes the element a queue.
static bool SelectsQueueElement(
    const Expr* sel,
    const std::unordered_map<std::string_view, ElaboratorData::VarArrayInfo>&
        arrays) {
  if (sel->index_end != nullptr || sel->base == nullptr ||
      sel->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto it = arrays.find(sel->base->text);
  return it != arrays.end() && it->second.elements_are_queues;
}

// Whether the innermost declaration of `name` among `decls` -- a block's, the
// walk's record of them -- is of an unpacked array; empty where no block the
// walk is inside declares it.
static std::optional<bool> BlockDeclIsArray(
    const std::vector<std::pair<std::string_view, bool>>& decls,
    std::string_view name) {
  for (auto it = decls.rbegin(); it != decls.rend(); ++it) {
    if (it->first == name) return it->second;
  }
  return std::nullopt;
}

// The elaborator classified a `{...}` right-hand side by its target and knew a
// bare name alone, so `h.q = {4, 5}` and `C::s = {5, 15, 25}` on a queue
// property were reported as vector concatenations of unsized constants where
// the same `q = {q, 6}` on a declared queue was admitted. The handle's class is
// what class_var_types_ records for the name, a module-scope handle's from
// ValidateVarDeclTypes and a block-local one's from WalkStmtsForClassHandleOps,
// which runs earlier in the validation order; `C::s` names the class itself.
// The member is then read off the class's declaration: a property with an
// unpacked dimension -- a queue's `[$]` among them -- is an unpacked array.
//
// §7.4 with §7.10 (printed pages 153 and 169): one element selected from an
// array whose elements are queues is a queue, so `fx[0] = {1, 2}` on `q_t
// fx[2]` under `typedef int q_t[$];`, `aa["k"] = {5}` on `q_t aa[string]` and
// `qq[0] = {qq[0], 5}` on `int qq[$][$]` assign unpacked array concatenations
// (§10.10, printed page 264), where each unsized item had been reported under
// §11.4.12.
bool ElaboratorOperationRules::IsUnpackedArrayConcatTarget(
    const Expr* lhs) const {
  if (lhs == nullptr) return false;
  if (lhs->kind == ExprKind::kIdentifier) {
    if (auto is_array = BlockDeclIsArray(block_decls_, lhs->text))
      return *is_array;
    return var_array_info_.count(lhs->text) > 0;
  }
  if (lhs->kind == ExprKind::kSelect)
    return SelectsQueueElement(lhs, var_array_info_);
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->rhs == nullptr || lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view cls_name;
  if (lhs->is_scope_resolution) {
    if (class_names_.count(lhs->lhs->text) == 0) return false;
    cls_name = lhs->lhs->text;
  } else {
    auto it = class_var_types_.find(lhs->lhs->text);
    if (it == class_var_types_.end()) return false;
    cls_name = it->second;
  }
  const ClassMember* prop =
      FindClassProperty(FindClassDecl(cls_name, unit_), lhs->rhs->text, unit_);
  return prop != nullptr && !prop->unpacked_dims.empty();
}

// §10.5 (printed page 256): a block item declaration's initializer is a
// procedural assignment to the variable it declares, so it is held to §11.4.12
// as `name = init` is, a `{...}` initializing an unpacked array being an
// unpacked array concatenation (§10.10, printed 264) whose items may be unsized
// -- as CheckVarInitUnsizedInConcat holds a module item's. The initializer of
// a block's declaration was never looked at, so `int x = {1, 2};` in a
// begin-end block went unreported.
void ElaboratorOperationRules::CheckBlockVarInitUnsizedInConcat(const Stmt* s) {
  if (s->kind != StmtKind::kVarDecl || s->var_init == nullptr) return;
  if (s->var_init->kind == ExprKind::kConcatenation &&
      !s->var_unpacked_dims.empty()) {
    for (auto* elem : s->var_init->elements) WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(s->var_init);
}

void ElaboratorOperationRules::WalkStmtsForUnsizedInConcat(const Stmt* s) {
  if (!s) return;
  CheckBlockVarInitUnsizedInConcat(s);

  bool is_array_concat_rhs = s->rhs &&
                             s->rhs->kind == ExprKind::kConcatenation &&
                             (s->kind == StmtKind::kBlockingAssign ||
                              s->kind == StmtKind::kNonblockingAssign) &&
                             IsUnpackedArrayConcatTarget(s->lhs);
  if (is_array_concat_rhs) {
    for (auto* elem : s->rhs->elements) WalkExprForUnsizedInConcat(elem);
  } else {
    WalkExprForUnsizedInConcat(s->rhs);
  }
  WalkExprForUnsizedInConcat(s->lhs);
  WalkExprForUnsizedInConcat(s->expr);
  WalkExprForUnsizedInConcat(s->condition);
  WalkExprForUnsizedInConcat(s->assert_expr);
  // §11.4.12 says "Unsized constant numbers shall not be allowed in
  // concatenations", a property of the concatenation and not of the statement
  // holding it, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `a = {x, 1}` written in a fork arm or in an
  // assertion action block was never looked at rather than looked at and
  // allowed.
  //
  // §10.10 with §7.10 (printed 264 and 169): a `{...}` assigned to an array a
  // block declares is an unpacked array concatenation as one assigned to a
  // module's is, so `begin int r[$]; r = {1, 2}; end` was reported under
  // §11.4.12. The declarations a statement's children make are forgotten when
  // the statement is left, and a declaration is recorded after its own
  // initializer is checked, which is written before it takes effect.
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForUnsizedInConcat(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

void ElaboratorOperationRules::ValidateUnsizedInConcat(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForUnsizedInConcat(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForUnsizedInConcat(item->assign_lhs);
      WalkExprForUnsizedInConcat(item->assign_rhs);
    }
    CheckVarInitUnsizedInConcat(item);
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.second);
  }
}

void ElaboratorOperationRules::CheckVarInitUnsizedInConcat(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  // §10.10: when the initializer of an array variable is a `{...}`
  // concatenation, it is an unpacked array concatenation where unsized integer
  // literals are legal — unlike a packed §11.4.12 concatenation. Descend into
  // the elements without applying the top-level unsized-constant check,
  // mirroring the procedural array-concat assignment path.
  if (item->init_expr->kind == ExprKind::kConcatenation &&
      var_array_info_.count(item->name)) {
    for (auto* elem : item->init_expr->elements)
      WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(item->init_expr);
}

}  // namespace delta
