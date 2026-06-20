#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

void Elaborator::CheckAssocOperandInBinaryExpr(const Expr* e) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary && !IsEqualityOp(e->op)) {
    for (const Expr* side : {e->lhs, e->rhs}) {
      if (!side || side->kind != ExprKind::kIdentifier) continue;
      auto it = var_array_info_.find(side->text);
      if (it == var_array_info_.end() || !it->second.is_assoc) continue;
      diag_.Error(side->range.start,
                  "associative array operand requires an element "
                  "selection before use in this expression");
    }
  }
  CheckAssocOperandInBinaryExpr(e->lhs);
  CheckAssocOperandInBinaryExpr(e->rhs);
  CheckAssocOperandInBinaryExpr(e->condition);
  CheckAssocOperandInBinaryExpr(e->true_expr);
  CheckAssocOperandInBinaryExpr(e->false_expr);
  CheckAssocOperandInBinaryExpr(e->base);
  CheckAssocOperandInBinaryExpr(e->index);
  CheckAssocOperandInBinaryExpr(e->index_end);
  for (const auto* a : e->args) CheckAssocOperandInBinaryExpr(a);
  for (const auto* el : e->elements) CheckAssocOperandInBinaryExpr(el);
}

void Elaborator::WalkStmtsForAssocOperand(const Stmt* s) {
  if (!s) return;
  CheckAssocOperandInBinaryExpr(s->rhs);
  CheckAssocOperandInBinaryExpr(s->expr);
  CheckAssocOperandInBinaryExpr(s->condition);
  CheckAssocOperandInBinaryExpr(s->for_cond);
  for (auto* sub : s->stmts) WalkStmtsForAssocOperand(sub);
  WalkStmtsForAssocOperand(s->then_branch);
  WalkStmtsForAssocOperand(s->else_branch);
  WalkStmtsForAssocOperand(s->body);
  WalkStmtsForAssocOperand(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssocOperand(ci.body);
}

void Elaborator::ValidateAssocOperandInExpr(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForAssocOperand(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssocOperandInBinaryExpr(item->assign_rhs);
    }
  }
}

namespace {
// Flags a single assignment-pattern item that names an array-typed identifier,
// which is illegal as an element of a pattern targeting an unpacked array.
void CheckArrayPatternIdentElem(
    const Expr* elem,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (elem->kind == ExprKind::kIdentifier && var_array_info.count(elem->text)) {
    diag.Error(elem->range.start,
               "array-typed identifier in assignment pattern targeting "
               "unpacked array");
  }
}
}  // namespace

void Elaborator::CheckArrayPatternElemTypeInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kAssignmentPattern) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.num_unpacked_dims != 1) return;

  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kReplicate) {
      for (auto* inner : elem->elements) {
        CheckArrayPatternIdentElem(inner, var_array_info_, diag_);
      }
    } else {
      CheckArrayPatternIdentElem(elem, var_array_info_, diag_);
    }
  }
}

void Elaborator::WalkStmtsForArrayPatternElemType(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayPatternElemTypeInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayPatternElemType(sub);
  WalkStmtsForArrayPatternElemType(s->then_branch);
  WalkStmtsForArrayPatternElemType(s->else_branch);
  WalkStmtsForArrayPatternElemType(s->body);
  WalkStmtsForArrayPatternElemType(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayPatternElemType(ci.body);
}

void Elaborator::ValidateArrayPatternElemType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForArrayPatternElemType(item->body);
    }
  }
}

void Elaborator::CheckReplicateTargetingArrayInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kReplicate) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  diag_.Error(s->rhs->range.start,
              "replication cannot target an unpacked array");
}

void Elaborator::WalkStmtsForReplicateTargetingArray(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckReplicateTargetingArrayInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForReplicateTargetingArray(sub);
  WalkStmtsForReplicateTargetingArray(s->then_branch);
  WalkStmtsForReplicateTargetingArray(s->else_branch);
  WalkStmtsForReplicateTargetingArray(s->body);
  WalkStmtsForReplicateTargetingArray(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForReplicateTargetingArray(ci.body);
}

void Elaborator::ValidateReplicateTargetingArray(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForReplicateTargetingArray(item->body);
    }
  }
}

// §11.5.2 — To express a bit-select or part-select of an array element, an
// address shall first be supplied for every dimension so that a single word is
// selected; only then may the bit-select or part-select be applied. A
// part-select that reaches a dimension which has not yet been addressed (for
// example threed_array[14][1][3:0] on a three-dimensional unpacked array, where
// the third dimension remains unaddressed) is illegal. We count the index
// selects sitting beneath the part-select down to the array's name; if that
// count falls short of the number of unpacked dimensions, the part-select lands
// on an unaddressed dimension and is rejected.
void Elaborator::CheckArrayElementPartSelectNode(const Expr* e) {
  uint32_t addressed = 0;
  const Expr* cur = e->base;
  std::string_view base_name;
  while (cur) {
    if (cur->kind == ExprKind::kSelect) {
      if (cur->index) ++addressed;
      cur = cur->base;
    } else if (cur->kind == ExprKind::kIdentifier) {
      base_name = cur->text;
      break;
    } else {
      return;  // base is not a plain array reference
    }
  }
  if (base_name.empty()) return;
  auto it = var_array_info_.find(base_name);
  if (it == var_array_info_.end()) return;
  const auto& info = it->second;
  if (info.is_dynamic || info.is_assoc) return;
  // Restrict to genuinely multidimensional arrays, the form the normative
  // example illustrates; single-dimension part-selects are governed elsewhere.
  if (info.num_unpacked_dims < 2) return;
  if (addressed < info.num_unpacked_dims) {
    diag_.Error(e->range.start,
                "part-select of an array element requires an address for each "
                "array dimension");
  }
}

void Elaborator::WalkExprForArrayElementPartSelect(const Expr* e) {
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

void Elaborator::WalkStmtsForArrayElementPartSelect(const Stmt* s) {
  if (!s) return;
  WalkExprForArrayElementPartSelect(s->rhs);
  WalkExprForArrayElementPartSelect(s->lhs);
  WalkExprForArrayElementPartSelect(s->expr);
  WalkExprForArrayElementPartSelect(s->condition);
  WalkExprForArrayElementPartSelect(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForArrayElementPartSelect(sub);
  WalkStmtsForArrayElementPartSelect(s->then_branch);
  WalkStmtsForArrayElementPartSelect(s->else_branch);
  WalkStmtsForArrayElementPartSelect(s->body);
  WalkStmtsForArrayElementPartSelect(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayElementPartSelect(ci.body);
}

void Elaborator::ValidateArrayElementPartSelect(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock;
    if (is_proc && item->body) {
      WalkStmtsForArrayElementPartSelect(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForArrayElementPartSelect(item->assign_rhs);
      WalkExprForArrayElementPartSelect(item->assign_lhs);
    }
  }
}

void Elaborator::CheckArrayConcatNestingInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.elem_type == DataTypeKind::kString) return;
  const auto& info = it->second;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kConcatenation) {
      if (info.num_unpacked_dims == 1 && info.elem_width > 0 &&
          InferExprWidth(elem, typedefs_) == info.elem_width) {
        continue;
      }
      diag_.Error(elem->range.start,
                  "nested concatenation in unpacked array "
                  "concatenation is not self-determined");
    }
  }
}

// Element types for which the literal `null` is a legal item in an unpacked
// array concatenation. Kinds outside this set make a null item illegal.
// `kNamed` is conservatively treated as legal because the named type could
// be a class or interface class; the elem-type record does not carry the
// resolved name, so we err on the permissive side rather than reject a
// legitimate class array.
static bool NullItemIsLegalForElemType(DataTypeKind k) {
  return k == DataTypeKind::kEvent || k == DataTypeKind::kChandle ||
         k == DataTypeKind::kVirtualInterface || k == DataTypeKind::kNamed;
}

void Elaborator::CheckNullItemInArrayConcatAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (NullItemIsLegalForElemType(it->second.elem_type)) return;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kIdentifier && elem->text == "null") {
      diag_.Error(elem->range.start,
                  "null is not a legal item in an unpacked array "
                  "concatenation for this target element type");
    }
  }
}

void Elaborator::WalkStmtsForArrayConcatNesting(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayConcatNestingInAssign(s);
    CheckNullItemInArrayConcatAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayConcatNesting(sub);
  WalkStmtsForArrayConcatNesting(s->then_branch);
  WalkStmtsForArrayConcatNesting(s->else_branch);
  WalkStmtsForArrayConcatNesting(s->body);
  WalkStmtsForArrayConcatNesting(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayConcatNesting(ci.body);
}

void Elaborator::ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForArrayConcatNesting(item->body);
    }
  }
}

namespace {
// Flags any unsized integer literal sitting directly inside a concatenation;
// such literals lack a self-determined width and are illegal there.
void CheckConcatElementsForUnsized(const Expr* concat, DiagEngine& diag) {
  for (auto* elem : concat->elements) {
    if (elem->kind == ExprKind::kIntegerLiteral) {
      auto tick = elem->text.find('\'');
      if (tick == std::string_view::npos || tick == 0) {
        diag.Error(elem->range.start,
                   "unsized constant is not allowed in a concatenation");
      }
    }
  }
}
}  // namespace

void Elaborator::WalkExprForUnsizedInConcat(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kConcatenation) {
    CheckConcatElementsForUnsized(expr, diag_);
  }
  WalkExprForUnsizedInConcat(expr->lhs);
  WalkExprForUnsizedInConcat(expr->rhs);
  WalkExprForUnsizedInConcat(expr->condition);
  WalkExprForUnsizedInConcat(expr->true_expr);
  WalkExprForUnsizedInConcat(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForUnsizedInConcat(elem);
  for (auto* arg : expr->args) WalkExprForUnsizedInConcat(arg);
}

void Elaborator::WalkStmtsForUnsizedInConcat(const Stmt* s) {
  if (!s) return;

  bool is_array_concat_rhs = s->rhs &&
                             s->rhs->kind == ExprKind::kConcatenation &&
                             s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
                             (s->kind == StmtKind::kBlockingAssign ||
                              s->kind == StmtKind::kNonblockingAssign) &&
                             var_array_info_.count(s->lhs->text);
  if (is_array_concat_rhs) {
    for (auto* elem : s->rhs->elements) WalkExprForUnsizedInConcat(elem);
  } else {
    WalkExprForUnsizedInConcat(s->rhs);
  }
  WalkExprForUnsizedInConcat(s->lhs);
  WalkExprForUnsizedInConcat(s->expr);
  WalkExprForUnsizedInConcat(s->condition);
  WalkExprForUnsizedInConcat(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForUnsizedInConcat(sub);
  WalkStmtsForUnsizedInConcat(s->then_branch);
  WalkStmtsForUnsizedInConcat(s->else_branch);
  WalkStmtsForUnsizedInConcat(s->body);
  WalkStmtsForUnsizedInConcat(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForUnsizedInConcat(ci.body);
}

void Elaborator::ValidateUnsizedInConcat(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForUnsizedInConcat(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForUnsizedInConcat(item->assign_lhs);
      WalkExprForUnsizedInConcat(item->assign_rhs);
    }
    if (item->init_expr) {
      WalkExprForUnsizedInConcat(item->init_expr);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.second);
  }
}

static bool IsSelectOnConcat(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  const Expr* base = expr->base;
  while (base && base->kind == ExprKind::kSelect) base = base->base;
  return base && base->kind == ExprKind::kConcatenation;
}

void Elaborator::CheckSelectOnConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (IsSelectOnConcat(lhs)) {
    diag_.Error(lhs->range.start,
                "select of a concatenation shall not be used as an lvalue");
  }
  if (lhs->kind == ExprKind::kConcatenation) {
    for (auto* elem : lhs->elements) CheckSelectOnConcatLvalue(elem);
  }
}

void Elaborator::WalkStmtsForSelectOnConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckSelectOnConcatLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForSelectOnConcatLvalue(sub);
  WalkStmtsForSelectOnConcatLvalue(s->then_branch);
  WalkStmtsForSelectOnConcatLvalue(s->else_branch);
  WalkStmtsForSelectOnConcatLvalue(s->body);
  WalkStmtsForSelectOnConcatLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForSelectOnConcatLvalue(ci.body);
}

void Elaborator::ValidateSelectOnConcatLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForSelectOnConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckSelectOnConcatLvalue(item->assign_lhs);
    }
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

void Elaborator::CheckReplicateLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (ExprContainsReplicate(lhs)) {
    diag_.Error(lhs->range.start,
                "replication shall not appear on the left-hand side "
                "of an assignment");
  }
}

void Elaborator::WalkStmtsForReplicateLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckReplicateLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForReplicateLvalue(sub);
  WalkStmtsForReplicateLvalue(s->then_branch);
  WalkStmtsForReplicateLvalue(s->else_branch);
  WalkStmtsForReplicateLvalue(s->body);
  WalkStmtsForReplicateLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForReplicateLvalue(ci.body);
}

void Elaborator::ValidateReplicateLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForReplicateLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckReplicateLvalue(item->assign_lhs);
    }
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
// Validates the repeat count of a single replication: it must not contain x/z
// and, when constant, must not be negative.
void CheckReplicateRepeatCount(const Expr* replicate, DiagEngine& diag) {
  const Expr* rc = replicate->repeat_count;
  if (RepeatCountHasXZ(rc)) {
    diag.Error(rc->range.start,
               "replication multiplier shall not contain x or z");
  } else {
    auto val = ConstEvalInt(rc);
    if (val) {
      if (*val < 0) {
        diag.Error(rc->range.start,
                   "replication multiplier shall not be negative");
      } else if (*val == 0) {
      }
    }
  }
}
}  // namespace

void Elaborator::WalkExprForReplicateMultiplier(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kReplicate) {
    CheckReplicateRepeatCount(expr, diag_);
  }
  WalkExprForReplicateMultiplier(expr->lhs);
  WalkExprForReplicateMultiplier(expr->rhs);
  WalkExprForReplicateMultiplier(expr->condition);
  WalkExprForReplicateMultiplier(expr->true_expr);
  WalkExprForReplicateMultiplier(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForReplicateMultiplier(elem);
  for (auto* arg : expr->args) WalkExprForReplicateMultiplier(arg);
}

static bool IsZeroReplicate(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kReplicate) return false;
  auto val = ConstEvalInt(expr->repeat_count);
  return val && *val == 0;
}

static void CheckZeroReplicateStandalone(const Expr* expr, DiagEngine& diag);

// True when a concatenation is non-empty and every operand is a zero
// replication, which leaves no positive-size operand to host them.
static bool ConcatIsAllZeroReplicate(const Expr* concat) {
  if (concat->elements.empty()) return false;
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem)) return false;
  }
  return true;
}

// Handles the concatenation arm of CheckZeroReplicateStandalone: a
// concatenation built entirely of zero replications is illegal, and any
// non-zero-replication operand is recursed into.
static void CheckZeroReplicateInConcat(const Expr* concat, DiagEngine& diag) {
  if (ConcatIsAllZeroReplicate(concat)) {
    diag.Error(concat->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size");
  }
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem)) {
      CheckZeroReplicateStandalone(elem, diag);
    }
  }
}

static void CheckZeroReplicateStandalone(const Expr* expr, DiagEngine& diag) {
  if (!expr) return;
  if (IsZeroReplicate(expr)) {
    diag.Error(expr->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size");
  }
  if (expr->kind == ExprKind::kConcatenation) {
    CheckZeroReplicateInConcat(expr, diag);
    return;
  }
  CheckZeroReplicateStandalone(expr->lhs, diag);
  CheckZeroReplicateStandalone(expr->rhs, diag);
  CheckZeroReplicateStandalone(expr->condition, diag);
  CheckZeroReplicateStandalone(expr->true_expr, diag);
  CheckZeroReplicateStandalone(expr->false_expr, diag);
  for (const auto* elem : expr->elements)
    CheckZeroReplicateStandalone(elem, diag);
  for (const auto* arg : expr->args) CheckZeroReplicateStandalone(arg, diag);
}

static void WalkStmtsForZeroReplicateStandalone(const Stmt* s,
                                                DiagEngine& diag) {
  if (!s) return;
  CheckZeroReplicateStandalone(s->rhs, diag);
  CheckZeroReplicateStandalone(s->lhs, diag);
  CheckZeroReplicateStandalone(s->expr, diag);
  CheckZeroReplicateStandalone(s->condition, diag);
  CheckZeroReplicateStandalone(s->assert_expr, diag);
  for (auto* sub : s->stmts) WalkStmtsForZeroReplicateStandalone(sub, diag);
  WalkStmtsForZeroReplicateStandalone(s->then_branch, diag);
  WalkStmtsForZeroReplicateStandalone(s->else_branch, diag);
  WalkStmtsForZeroReplicateStandalone(s->body, diag);
  WalkStmtsForZeroReplicateStandalone(s->for_body, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForZeroReplicateStandalone(ci.body, diag);
}

void Elaborator::WalkStmtsForReplicateMultiplier(const Stmt* s) {
  if (!s) return;
  WalkExprForReplicateMultiplier(s->rhs);
  WalkExprForReplicateMultiplier(s->lhs);
  WalkExprForReplicateMultiplier(s->expr);
  WalkExprForReplicateMultiplier(s->condition);
  WalkExprForReplicateMultiplier(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForReplicateMultiplier(sub);
  WalkStmtsForReplicateMultiplier(s->then_branch);
  WalkStmtsForReplicateMultiplier(s->else_branch);
  WalkStmtsForReplicateMultiplier(s->body);
  WalkStmtsForReplicateMultiplier(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForReplicateMultiplier(ci.body);
}

void Elaborator::ValidateReplicateMultiplier(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForReplicateMultiplier(item->body);
      WalkStmtsForZeroReplicateStandalone(item->body, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForReplicateMultiplier(item->assign_lhs);
      WalkExprForReplicateMultiplier(item->assign_rhs);
      CheckZeroReplicateStandalone(item->assign_lhs, diag_);
      CheckZeroReplicateStandalone(item->assign_rhs, diag_);
    }
    if (item->init_expr) {
      WalkExprForReplicateMultiplier(item->init_expr);
      CheckZeroReplicateStandalone(item->init_expr, diag_);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForReplicateMultiplier(p.second);
    CheckZeroReplicateStandalone(p.second, diag_);
  }
}

}  // namespace delta
