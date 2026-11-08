#include <algorithm>
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
#include "parser/ast_type.h"

namespace delta {

namespace {
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
  if (expr->kind == ExprKind::kConcatenation ||
      (expr->kind == ExprKind::kReplicate && !expr->is_pattern_replication)) {
    CheckConcatElementsForUnsized(expr, diag_);
  }
  WalkExprForUnsizedInConcat(expr->lhs);
  WalkExprForUnsizedInConcat(expr->rhs);
  WalkExprForUnsizedInConcat(expr->condition);
  WalkExprForUnsizedInConcat(expr->true_expr);
  WalkExprForUnsizedInConcat(expr->false_expr);
  for (auto* elem : expr->elements) {
    if (expr->kind == ExprKind::kAssignmentPattern &&
        elem->kind == ExprKind::kConcatenation) {
      for (auto* sub : elem->elements) WalkExprForUnsizedInConcat(sub);
      continue;
    }
    WalkExprForUnsizedInConcat(elem);
  }
  for (auto* arg : expr->args) WalkExprForUnsizedInConcat(arg);
}

static const ClassMember* FindClassProperty(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c != nullptr; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty && !m->is_param &&
          m->name == name) {
        return m;
      }
    }
  }
  return nullptr;
}

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

static std::optional<bool> BlockDeclIsArray(
    const std::vector<std::pair<std::string_view, bool>>& decls,
    std::string_view name) {
  for (auto it = decls.rbegin(); it != decls.rend(); ++it) {
    if (it->first == name) return it->second;
  }
  return std::nullopt;
}

bool ElaboratorOperationRules::SelectsArrayElementArray(const Expr* sel) const {
  if (SelectsQueueElement(sel, var_array_info_)) return true;
  size_t selects = 0;
  for (; sel->kind == ExprKind::kSelect; sel = sel->base) ++selects;
  if (sel->kind != ExprKind::kIdentifier) return false;
  auto it = var_array_info_.find(sel->text);
  return it != var_array_info_.end() && it->second.num_unpacked_dims > selects;
}

std::optional<bool> ElaboratorOperationRules::StructMemberIsArray(
    const Expr* lhs) const {
  auto st = concat_target_types_.find(lhs->lhs->text);
  if (st == concat_target_types_.end()) return std::nullopt;
  const std::vector<StructMember>* members =
      StructMembersOf(*st->second, typedefs_);
  if (members == nullptr) return std::nullopt;
  return std::ranges::any_of(*members, [&](const StructMember& m) {
    return m.name == lhs->rhs->text && !m.unpacked_dims.empty();
  });
}

bool ElaboratorOperationRules::IsUnpackedArrayConcatTarget(
    const Expr* lhs) const {
  if (lhs == nullptr) return false;
  if (lhs->kind == ExprKind::kIdentifier) {
    if (auto is_array = BlockDeclIsArray(block_decls_, lhs->text))
      return *is_array;
    return var_array_info_.count(lhs->text) > 0;
  }
  if (lhs->kind == ExprKind::kSelect) return SelectsArrayElementArray(lhs);
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->rhs == nullptr || lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (auto member_array = StructMemberIsArray(lhs)) return *member_array;
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

void ElaboratorOperationRules::CheckBlockVarInitUnsizedInConcat(const Stmt* s) {
  if (s->kind != StmtKind::kVarDecl || s->var_init == nullptr) return;
  if (s->var_init->kind == ExprKind::kConcatenation &&
      !s->var_unpacked_dims.empty()) {
    for (auto* elem : s->var_init->elements) WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(s->var_init);
}

void ElaboratorOperationRules::WalkItemsOrExprForUnsizedInConcat(
    const Expr* e, bool is_array_concat) {
  if (!is_array_concat) {
    WalkExprForUnsizedInConcat(e);
    return;
  }
  for (auto* elem : e->elements) WalkExprForUnsizedInConcat(elem);
}

void ElaboratorOperationRules::WalkStmtsForUnsizedInConcat(const Stmt* s) {
  if (!s) return;
  CheckBlockVarInitUnsizedInConcat(s);

  bool is_concat_assign = s->rhs && s->rhs->kind == ExprKind::kConcatenation &&
                          (s->kind == StmtKind::kBlockingAssign ||
                           s->kind == StmtKind::kNonblockingAssign);
  bool is_array_concat_rhs =
      is_concat_assign && IsUnpackedArrayConcatTarget(s->lhs);
  if (is_concat_assign && !is_array_concat_rhs && s->rhs->elements.empty() &&
      s->lhs->kind == ExprKind::kIdentifier) {
    diag_.Error(s->rhs->range.start,
                "an empty concatenation, {}, is assigned only to an unpacked "
                "array",
                Subclause("10.10"));
  }
  WalkItemsOrExprForUnsizedInConcat(s->rhs, is_array_concat_rhs);
  WalkExprForUnsizedInConcat(s->lhs);
  WalkItemsOrExprForUnsizedInConcat(
      s->expr, s->kind == StmtKind::kReturn && returns_unpacked_array_ &&
                   s->expr->kind == ExprKind::kConcatenation);
  WalkExprForUnsizedInConcat(s->condition);
  WalkExprForUnsizedInConcat(s->assert_expr);
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForUnsizedInConcat(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

void ElaboratorOperationRules::ValidateUnsizedInConcat(const ModuleDecl* decl) {
  concat_target_types_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl)
      concat_target_types_[item->name] = &item->data_type;
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForUnsizedInConcat(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign)
      CheckContAssignUnsizedInConcat(item);
    CheckVarInitUnsizedInConcat(item);
    returns_unpacked_array_ = !item->return_array_dims.empty();
    for (const auto& arg : item->func_args)
      block_decls_.emplace_back(arg.name, !arg.unpacked_dims.empty());
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForUnsizedInConcat(s);
    block_decls_.clear();
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.second);
  }
}

void ElaboratorOperationRules::CheckContAssignUnsizedInConcat(
    const ModuleItem* item) {
  WalkExprForUnsizedInConcat(item->assign_lhs);
  const Expr* rhs = item->assign_rhs;
  if (rhs->kind == ExprKind::kConcatenation &&
      IsUnpackedArrayConcatTarget(item->assign_lhs)) {
    for (auto* elem : rhs->elements) WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(rhs);
}

void ElaboratorOperationRules::CheckVarInitUnsizedInConcat(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind == ExprKind::kConcatenation &&
      var_array_info_.count(item->name)) {
    for (auto* elem : item->init_expr->elements)
      WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(item->init_expr);
}

}  // namespace delta
