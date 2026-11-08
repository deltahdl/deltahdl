#include <algorithm>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {
void CheckArrayPatternIdentElem(
    const Expr* elem,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (elem->kind == ExprKind::kIdentifier && var_array_info.count(elem->text)) {
    diag.Error(elem->range.start,
               "array-typed identifier in assignment pattern targeting "
               "unpacked array",
               Subclause("10.9.1"));
  }
}

void ScanArrayPatternElems(
    const Expr* pattern,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  for (auto* elem : pattern->elements) {
    if (elem->kind == ExprKind::kReplicate) {
      for (auto* inner : elem->elements) {
        CheckArrayPatternIdentElem(inner, var_array_info, diag);
      }
    } else {
      CheckArrayPatternIdentElem(elem, var_array_info, diag);
    }
  }
}
}  // namespace

void ElaboratorOperationRules::CheckArrayPatternElemTypeInAssign(
    const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kAssignmentPattern) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.num_unpacked_dims != 1) return;

  ScanArrayPatternElems(s->rhs, var_array_info_, diag_);
}

void ElaboratorOperationRules::CheckArrayPatternElemTypeInInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  auto it = var_array_info_.find(item->name);
  if (it == var_array_info_.end()) return;
  if (it->second.num_unpacked_dims != 1) return;

  ScanArrayPatternElems(item->init_expr, var_array_info_, diag_);
}

void ElaboratorOperationRules::WalkStmtsForArrayPatternElemType(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayPatternElemTypeInAssign(s);
  }
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayPatternElemType(sub); });
}

void ElaboratorOperationRules::ValidateArrayPatternElemType(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForArrayPatternElemType(item->body);
    }
    CheckArrayPatternElemTypeInInit(item);
  }
}

void ElaboratorOperationRules::CheckReplicateTargetingArrayInAssign(
    const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kReplicate) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  diag_.Error(s->rhs->range.start,
              "replication cannot target an unpacked array",
              Subclause("10.10.1"));
}

void ElaboratorOperationRules::CheckReplicateTargetingArrayInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kReplicate) return;
  if (var_array_info_.find(item->name) == var_array_info_.end()) return;
  diag_.Error(item->init_expr->range.start,
              "replication cannot target an unpacked array",
              Subclause("10.10.1"));
}

void ElaboratorOperationRules::WalkStmtsForReplicateTargetingArray(
    const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckReplicateTargetingArrayInAssign(s);
  }
  ForEachChildStmt(s, [this](Stmt* const& sub) {
    WalkStmtsForReplicateTargetingArray(sub);
  });
}

void ElaboratorOperationRules::ValidateReplicateTargetingArray(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForReplicateTargetingArray(item->body);
    }
    CheckReplicateTargetingArrayInit(item);
  }
}

namespace {

struct AddressedDims {
  uint32_t count = 0;
  std::string_view array_name;
};

AddressedDims CountAddressedDims(const Expr* base) {
  AddressedDims addressed;
  for (const Expr* cur = base; cur != nullptr; cur = cur->base) {
    if (cur->kind == ExprKind::kIdentifier) {
      addressed.array_name = cur->text;
      break;
    }
    if (cur->kind != ExprKind::kSelect) break;
    if (cur->index) ++addressed.count;
  }
  return addressed;
}

}  // namespace

void ElaboratorOperationRules::CheckArrayElementPartSelectNode(const Expr* e) {
  AddressedDims addressed = CountAddressedDims(e->base);
  if (addressed.array_name.empty()) return;
  const VarArrayInfo* found = nullptr;
  if (auto it = var_array_info_.find(addressed.array_name);
      it != var_array_info_.end()) {
    found = &it->second;
  } else if (auto nit = net_array_info_.find(addressed.array_name);
             nit != net_array_info_.end()) {
    found = &nit->second;
  }
  if (found == nullptr) return;
  const auto& info = *found;
  if (info.is_dynamic || info.is_assoc) return;
  if (addressed.count >= info.num_unpacked_dims) return;
  if (e->is_part_select_plus || e->is_part_select_minus) return;
  if (info.declared_dims.size() != info.num_unpacked_dims) return;
  auto first = ConstEvalInt(e->index);
  auto second = ConstEvalInt(e->index_end);
  if (!first || !second) return;
  const auto& sliced = info.declared_dims[addressed.count];
  bool reversed =
      sliced.IsDescending() ? (*first < *second) : (*first > *second);
  if (reversed) {
    diag_.Error(e->range.start,
                "slice's first index must address a more significant element "
                "than its second index",
                Subclause("11.5.2"));
  }
}

void ElaboratorOperationRules::WalkExprForArrayElementPartSelect(
    const Expr* e) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect &&
      (e->index_end || e->is_part_select_plus || e->is_part_select_minus)) {
    CheckArrayElementPartSelectNode(e);
  }
  WalkExprForArrayElementPartSelect(e->lhs);
  WalkExprForArrayElementPartSelect(e->rhs);
  WalkExprForArrayElementPartSelect(e->base);
  WalkExprForArrayElementPartSelect(e->index);
  WalkExprForArrayElementPartSelect(e->index_end);
  WalkExprForArrayElementPartSelect(e->condition);
  WalkExprForArrayElementPartSelect(e->true_expr);
  WalkExprForArrayElementPartSelect(e->false_expr);
  for (auto* elem : e->elements) WalkExprForArrayElementPartSelect(elem);
  for (auto* arg : e->args) WalkExprForArrayElementPartSelect(arg);
}

void ElaboratorOperationRules::WalkStmtsForArrayElementPartSelect(
    const Stmt* s) {
  if (!s) return;
  WalkExprForArrayElementPartSelect(s->rhs);
  WalkExprForArrayElementPartSelect(s->lhs);
  WalkExprForArrayElementPartSelect(s->expr);
  WalkExprForArrayElementPartSelect(s->condition);
  WalkExprForArrayElementPartSelect(s->assert_expr);
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayElementPartSelect(sub); });
}

void ElaboratorOperationRules::ValidateArrayElementPartSelect(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForArrayElementPartSelect(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForArrayElementPartSelect(item->assign_rhs);
      WalkExprForArrayElementPartSelect(item->assign_lhs);
    }
  }
}

void ElaboratorOperationRules::CheckNestedArrayConcatItems(const Expr* concat) {
  for (const Expr* elem : concat->elements) {
    if (elem->kind != ExprKind::kConcatenation) continue;
    bool holds_array =
        std::ranges::any_of(elem->elements, [this](const Expr* inner) {
          return inner->kind == ExprKind::kIdentifier &&
                 var_array_info_.count(inner->text) != 0;
        });
    if (!holds_array) continue;
    diag_.Error(elem->range.start,
                "nested concatenation in unpacked array "
                "concatenation is not self-determined",
                Subclause("10.10.3"));
  }
}

void ElaboratorOperationRules::CheckArrayConcatNestingInAssign(const Stmt* s) {
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  if (var_array_info_.count(s->lhs->text) == 0) return;
  CheckNestedArrayConcatItems(s->rhs);
}

static bool NullItemIsLegalForElemType(DataTypeKind k) {
  return k == DataTypeKind::kEvent || k == DataTypeKind::kChandle ||
         k == DataTypeKind::kVirtualInterface || k == DataTypeKind::kNamed;
}

void ElaboratorOperationRules::CheckArrayConcatItemTypes(
    const Expr* concat, const VarArrayInfo& info) {
  bool handle_elems = NullItemIsLegalForElemType(info.elem_type);
  for (const Expr* elem : concat->elements) {
    if (elem->kind != ExprKind::kIdentifier || handle_elems) continue;
    if (elem->text == "null") {
      diag_.Error(elem->range.start,
                  "null is not a legal item in an unpacked array "
                  "concatenation for this target element type",
                  Subclause("10.10"));
    } else if (class_var_types_.count(elem->text) != 0) {
      diag_.Error(elem->range.start,
                  std::format("class handle '{}' is not assignment compatible "
                              "with the elements of the unpacked array "
                              "concatenation's target",
                              elem->text),
                  Subclause("10.10"));
    }
  }
}

void ElaboratorOperationRules::CheckNullItemInArrayConcatAssign(const Stmt* s) {
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  CheckArrayConcatItemTypes(s->rhs, it->second);
}

void ElaboratorOperationRules::CheckArrayConcatNestingInInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(item->name);
  if (it == var_array_info_.end()) return;
  CheckNestedArrayConcatItems(item->init_expr);
  CheckArrayConcatItemTypes(item->init_expr, it->second);
}

void ElaboratorOperationRules::WalkStmtsForArrayConcatNesting(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayConcatNestingInAssign(s);
    CheckNullItemInArrayConcatAssign(s);
  }
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayConcatNesting(sub); });
}

void ElaboratorOperationRules::ValidateUnpackedArrayConcatNesting(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForArrayConcatNesting(item->body);
    }
    CheckArrayConcatNestingInInit(item);
  }
}

namespace {

const Expr* AssignedOperand(const Expr* e) {
  switch (e->kind) {
    case ExprKind::kPostfixUnary:
      return e->lhs;
    case ExprKind::kUnary:
      return e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus
                 ? e->lhs
                 : nullptr;
    case ExprKind::kBinary:
      return e->op == TokenKind::kEq || IsCompoundAssignOp(e->op) ? e->lhs
                                                                  : nullptr;
    default:
      return nullptr;
  }
}

template <typename Fn>
void ForEachAssignedOperand(const Stmt* s, const Fn& fn) {
  auto visit = [&](const Expr* e) {
    const Expr* target = AssignedOperand(e);
    if (target != nullptr && target != s->lhs) fn(target);
  };
  ForEachChildExpr(s, [&](const Expr* root) { ForEachExprUnder(root, visit); });
}

}  // namespace

static bool IsSelectOnConcat(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  const Expr* base = expr->base;
  while (base && base->kind == ExprKind::kSelect) base = base->base;
  return base && base->kind == ExprKind::kConcatenation;
}

void ElaboratorOperationRules::CheckSelectOnConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (IsSelectOnConcat(lhs)) {
    diag_.Error(lhs->range.start,
                "select of a concatenation shall not be used as an lvalue",
                Subclause("11.4.12"));
  }
  if (lhs->kind == ExprKind::kConcatenation) {
    for (auto* elem : lhs->elements) CheckSelectOnConcatLvalue(elem);
  }
}

void ElaboratorOperationRules::WalkStmtsForSelectOnConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckSelectOnConcatLvalue(s->lhs);
  }
  ForEachAssignedOperand(
      s, [this](const Expr* target) { CheckSelectOnConcatLvalue(target); });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForSelectOnConcatLvalue(sub); });
}

void ElaboratorOperationRules::ValidateSelectOnConcatLvalue(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForSelectOnConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckSelectOnConcatLvalue(item->assign_lhs);
    }
    for (const Stmt* s : item->func_body_stmts)
      WalkStmtsForSelectOnConcatLvalue(s);
  }
}

static bool ExprContainsReplicate(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kReplicate) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ExprContainsReplicate(elem)) return true;
    }
  }
  return false;
}

void ElaboratorOperationRules::CheckReplicateLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (ExprContainsReplicate(lhs)) {
    diag_.Error(lhs->range.start,
                "an assignment target cannot contain a replication",
                Subclause("11.4.12.1"));
  }
}

void ElaboratorOperationRules::WalkStmtsForReplicateLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckReplicateLvalue(s->lhs);
  }
  ForEachAssignedOperand(
      s, [this](const Expr* target) { CheckReplicateLvalue(target); });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForReplicateLvalue(sub); });
}

void ElaboratorOperationRules::ValidateReplicateLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForReplicateLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckReplicateLvalue(item->assign_lhs);
    }
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForReplicateLvalue(s);
  }
}

static bool RepeatCountHasXZ(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIntegerLiteral) {
    auto apos = e->text.find('\'');
    if (apos != std::string_view::npos) {
      return e->text.substr(apos + 1).find_first_of("xXzZ") !=
             std::string_view::npos;
    }
  }
  return false;
}

namespace {
bool MayReplicateAString(
    const Expr* replicate,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types) {
  return std::ranges::any_of(replicate->elements, [&](const Expr* e) {
    if (e->kind == ExprKind::kStringLiteral) return true;
    auto it = var_types.find(ExprIdent(e));
    return it != var_types.end() && it->second == DataTypeKind::kString;
  });
}

void CheckReplicateRepeatCount(
    const Expr* replicate, const ScopeMap& scope,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    DiagEngine& diag) {
  const Expr* rc = replicate->repeat_count;
  if (RepeatCountHasXZ(rc)) {
    diag.Error(rc->range.start,
               "replication multiplier shall not contain x or z",
               Subclause("11.4.12.1"));
    return;
  }
  if (!IsConstantExpr(rc, scope) &&
      !MayReplicateAString(replicate, var_types)) {
    diag.Error(rc->range.start,
               "replication multiplier shall be a constant expression",
               Subclause("11.4.12.1"));
    return;
  }
  auto val = ConstEvalInt(rc, scope);
  if (val && *val < 0) {
    diag.Error(rc->range.start, "replication multiplier shall not be negative",
               Subclause("11.4.12.1"));
  }
}
}  // namespace

void ElaboratorOperationRules::WalkExprForReplicateMultiplier(
    const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kReplicate) {
    CheckReplicateRepeatCount(expr, replicate_multiplier_scope_, var_types_,
                              diag_);
  }
  WalkExprForReplicateMultiplier(expr->lhs);
  WalkExprForReplicateMultiplier(expr->rhs);
  WalkExprForReplicateMultiplier(expr->condition);
  WalkExprForReplicateMultiplier(expr->true_expr);
  WalkExprForReplicateMultiplier(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForReplicateMultiplier(elem);
  for (auto* arg : expr->args) WalkExprForReplicateMultiplier(arg);
}

static bool IsZeroReplicate(const Expr* expr, const ScopeMap& scope) {
  if (!expr || expr->kind != ExprKind::kReplicate) return false;
  auto val = ConstEvalInt(expr->repeat_count, scope);
  return val && *val == 0;
}

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         const ScopeMap& scope,
                                         DiagEngine& diag);

static bool ConcatIsAllZeroReplicate(const Expr* concat,
                                     const ScopeMap& scope) {
  if (concat->elements.empty()) return false;
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem, scope)) return false;
  }
  return true;
}

static void CheckZeroReplicateInConcat(const Expr* concat,
                                       const ScopeMap& scope,
                                       DiagEngine& diag) {
  if (ConcatIsAllZeroReplicate(concat, scope)) {
    diag.Error(concat->range.start,
               "a zero replication needs a positive-size operand beside it "
               "in the same concatenation",
               Subclause("11.4.12.1"));
  }
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem, scope)) {
      CheckZeroReplicateStandalone(elem, scope, diag);
    }
  }
}

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         const ScopeMap& scope,
                                         DiagEngine& diag) {
  if (!expr) return;
  if (IsZeroReplicate(expr, scope)) {
    diag.Error(expr->range.start,
               "a zero replication needs a positive-size operand beside it "
               "in the same concatenation",
               Subclause("11.4.12.1"));
  }
  if (expr->kind == ExprKind::kConcatenation ||
      expr->kind == ExprKind::kReplicate) {
    CheckZeroReplicateInConcat(expr, scope, diag);
    return;
  }
  CheckZeroReplicateStandalone(expr->lhs, scope, diag);
  CheckZeroReplicateStandalone(expr->rhs, scope, diag);
  CheckZeroReplicateStandalone(expr->condition, scope, diag);
  CheckZeroReplicateStandalone(expr->true_expr, scope, diag);
  CheckZeroReplicateStandalone(expr->false_expr, scope, diag);
  for (const auto* elem : expr->elements)
    CheckZeroReplicateStandalone(elem, scope, diag);
  for (const auto* arg : expr->args)
    CheckZeroReplicateStandalone(arg, scope, diag);
}

static void WalkStmtsForZeroReplicateStandalone(const Stmt* s,
                                                const ScopeMap& scope,
                                                DiagEngine& diag) {
  if (!s) return;
  CheckZeroReplicateStandalone(s->rhs, scope, diag);
  CheckZeroReplicateStandalone(s->lhs, scope, diag);
  CheckZeroReplicateStandalone(s->expr, scope, diag);
  CheckZeroReplicateStandalone(s->condition, scope, diag);
  CheckZeroReplicateStandalone(s->assert_expr, scope, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForZeroReplicateStandalone(sub, scope, diag);
  });
}

void ElaboratorOperationRules::WalkStmtsForReplicateMultiplier(const Stmt* s) {
  if (!s) return;
  WalkExprForReplicateMultiplier(s->rhs);
  WalkExprForReplicateMultiplier(s->lhs);
  WalkExprForReplicateMultiplier(s->expr);
  WalkExprForReplicateMultiplier(s->condition);
  WalkExprForReplicateMultiplier(s->assert_expr);
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForReplicateMultiplier(sub); });
}

void ElaboratorOperationRules::ValidateReplicateMultiplier(
    const ModuleDecl* decl) {
  const ScopeMap& scope = replicate_multiplier_scope_;
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForReplicateMultiplier(item->body);
      WalkStmtsForZeroReplicateStandalone(item->body, scope, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForReplicateMultiplier(item->assign_lhs);
      WalkExprForReplicateMultiplier(item->assign_rhs);
      CheckZeroReplicateStandalone(item->assign_lhs, scope, diag_);
      CheckZeroReplicateStandalone(item->assign_rhs, scope, diag_);
    }
    if (item->init_expr) {
      WalkExprForReplicateMultiplier(item->init_expr);
      CheckZeroReplicateStandalone(item->init_expr, scope, diag_);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForReplicateMultiplier(p.second);
    CheckZeroReplicateStandalone(p.second, scope, diag_);
  }
}

}  // namespace delta
