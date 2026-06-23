#include <charconv>
#include <format>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static std::string_view AggregateOperandName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect &&
      (e->index_end || e->is_part_select_plus || e->is_part_select_minus) &&
      e->base && e->base->kind == ExprKind::kIdentifier) {
    return e->base->text;
  }
  return {};
}

using NameMap = std::unordered_map<std::string_view, std::string_view>;
using WidthMap = std::unordered_map<std::string_view, uint32_t>;

// Two whole unpacked-array operands compare legally only when their element
// type and dimension sizes match (§6.22.2). A typedef array's dimensions are
// not recorded on the variable, so use the typedef's cached fixed unpacked
// width as the shape key: differing widths are necessarily non-equivalent.
// Returns true when both operands are unpacked-array typedef variables, i.e.
// the comparison was fully handled here.
static bool CheckArrayCompareOp(const Expr* expr, const NameMap& types,
                                const WidthMap& widths, DiagEngine& diag) {
  if (expr->lhs->kind != ExprKind::kIdentifier ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto lt = types.find(AggregateOperandName(expr->lhs));
  auto rt = types.find(AggregateOperandName(expr->rhs));
  if (lt == types.end() || rt == types.end()) return false;
  auto lw = widths.find(lt->second);
  auto rw = widths.find(rt->second);
  if (lw == widths.end() || rw == widths.end()) return false;
  if (lw->second != rw->second) {
    diag.Error(expr->range.start,
               "comparison of non-equivalent aggregate array types");
  }
  return true;
}

void Elaborator::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  auto l_name = AggregateOperandName(expr->lhs);
  auto r_name = AggregateOperandName(expr->rhs);
  if (l_name.empty() || r_name.empty()) return;
  if (CheckArrayCompareOp(expr, var_named_types_,
                          fixed_unpacked_typedef_widths_, diag_)) {
    return;
  }

  auto lit = var_named_types_.find(l_name);
  auto rit = var_named_types_.find(r_name);
  if (lit == var_named_types_.end() || rit == var_named_types_.end()) return;
  if (lit->second == rit->second) return;

  auto is_aggregate_var = [&](std::string_view name,
                              std::string_view type_name) {
    if (var_array_info_.count(name)) return true;
    auto it = typedefs_.find(type_name);
    return it != typedefs_.end() && IsAggregateType(it->second);
  };
  if (!is_aggregate_var(l_name, lit->second)) return;
  if (!is_aggregate_var(r_name, rit->second)) return;

  diag_.Error(expr->range.start,
              std::format("comparison of non-equivalent aggregate "
                          "types '{}' and '{}'",
                          lit->second, rit->second));
}

void Elaborator::WalkExprForAggregateCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary &&
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq)) {
    CheckAggregateCompareOp(expr);
  }
  WalkExprForAggregateCompare(expr->lhs);
  WalkExprForAggregateCompare(expr->rhs);
  WalkExprForAggregateCompare(expr->condition);
  WalkExprForAggregateCompare(expr->true_expr);
  WalkExprForAggregateCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForAggregateCompare(elem);
  for (auto* arg : expr->args) WalkExprForAggregateCompare(arg);
}

void Elaborator::WalkStmtsForAggregateCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForAggregateCompare(s->rhs);
  WalkExprForAggregateCompare(s->lhs);
  WalkExprForAggregateCompare(s->expr);
  WalkExprForAggregateCompare(s->condition);
  WalkExprForAggregateCompare(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForAggregateCompare(sub);
  WalkStmtsForAggregateCompare(s->then_branch);
  WalkStmtsForAggregateCompare(s->else_branch);
  WalkStmtsForAggregateCompare(s->body);
  WalkStmtsForAggregateCompare(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAggregateCompare(ci.body);
}

void Elaborator::ValidateAggregateComparisons(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForAggregateCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAggregateCompare(item->assign_rhs);
    }
  }
}

// §6.23 — A type reference used in an equality, inequality, case-equality,
// or case-inequality comparison shall only be compared with another type
// reference. Reject any such comparison whose other operand is a value
// expression rather than a kTypeRef node.
void Elaborator::CheckTypeRefCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  bool lhs_is_type = expr->lhs->kind == ExprKind::kTypeRef;
  bool rhs_is_type = expr->rhs->kind == ExprKind::kTypeRef;
  if (lhs_is_type == rhs_is_type) return;
  diag_.Error(expr->range.start,
              "type reference may be compared only with another type "
              "reference");
}

void Elaborator::WalkExprForTypeRefCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool is_equality =
        expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq ||
        expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq;
    if (is_equality) {
      CheckTypeRefCompareOp(expr);
    } else if ((expr->lhs && expr->lhs->kind == ExprKind::kTypeRef) ||
               (expr->rhs && expr->rhs->kind == ExprKind::kTypeRef)) {
      // §A.10: a type_reference primary is restricted to the equality,
      // inequality, case-equality, and case-inequality operators (and to use
      // as the casting type of a static cast, which is not a binary operator).
      // Any other operator applied to a type_reference is illegal.
      diag_.Error(expr->range.start,
                  "a type reference may only be used with the equality, "
                  "inequality, and case equality/inequality operators");
    }
  }
  WalkExprForTypeRefCompare(expr->lhs);
  WalkExprForTypeRefCompare(expr->rhs);
  WalkExprForTypeRefCompare(expr->condition);
  WalkExprForTypeRefCompare(expr->true_expr);
  WalkExprForTypeRefCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefCompare(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefCompare(arg);
}

void Elaborator::WalkStmtsForTypeRefCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForTypeRefCompare(s->rhs);
  WalkExprForTypeRefCompare(s->lhs);
  WalkExprForTypeRefCompare(s->expr);
  WalkExprForTypeRefCompare(s->condition);
  WalkExprForTypeRefCompare(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForTypeRefCompare(sub);
  WalkStmtsForTypeRefCompare(s->then_branch);
  WalkStmtsForTypeRefCompare(s->else_branch);
  WalkStmtsForTypeRefCompare(s->body);
  WalkStmtsForTypeRefCompare(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForTypeRefCompare(ci.body);
}

void Elaborator::ValidateTypeRefComparisons(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForTypeRefCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForTypeRefCompare(item->assign_rhs);
    }
  }
}

// §6.23 — the expression supplied to the type operator shall not contain a
// hierarchical reference or a reference to an element of a dynamic object.
// A member-access subtree is treated as a hierarchical reference; a select
// whose base names a dynamic array or associative array is treated as a
// reference to a dynamic-object element.
static bool TypeRefArgHasMemberAccess(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (TypeRefArgHasMemberAccess(e->lhs)) return true;
  if (TypeRefArgHasMemberAccess(e->rhs)) return true;
  if (TypeRefArgHasMemberAccess(e->base)) return true;
  if (TypeRefArgHasMemberAccess(e->index)) return true;
  if (TypeRefArgHasMemberAccess(e->condition)) return true;
  if (TypeRefArgHasMemberAccess(e->true_expr)) return true;
  if (TypeRefArgHasMemberAccess(e->false_expr)) return true;
  for (const auto* elem : e->elements) {
    if (TypeRefArgHasMemberAccess(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgHasMemberAccess(arg)) return true;
  }
  return false;
}

// True when this node is itself a select on a dynamic/associative array; the
// recursive descent into children is handled separately by the caller.
static bool TypeRefArgSelectsDynamicElement(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        array_info) {
  if (e->kind != ExprKind::kSelect || !e->base ||
      e->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto it = array_info.find(e->base->text);
  return it != array_info.end() &&
         (it->second.is_dynamic || it->second.is_assoc);
}

bool Elaborator::TypeRefArgUsesDynamicElement(const Expr* e) const {
  if (!e) return false;
  if (TypeRefArgSelectsDynamicElement(e, var_array_info_)) return true;
  const Expr* const kChildren[] = {e->lhs,       e->rhs,       e->base,
                                   e->index,     e->condition, e->true_expr,
                                   e->false_expr};
  for (const Expr* child : kChildren) {
    if (TypeRefArgUsesDynamicElement(child)) return true;
  }
  for (const auto* elem : e->elements) {
    if (TypeRefArgUsesDynamicElement(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgUsesDynamicElement(arg)) return true;
  }
  return false;
}

void Elaborator::CheckTypeRefArgInner(const Expr* inner, SourceLoc loc) {
  if (!inner) return;
  if (TypeRefArgHasMemberAccess(inner)) {
    diag_.Error(loc,
                "type operator argument shall not contain a hierarchical "
                "reference");
    return;
  }
  if (TypeRefArgUsesDynamicElement(inner)) {
    diag_.Error(loc,
                "type operator argument shall not reference elements of "
                "dynamic objects");
  }
}

void Elaborator::WalkExprForTypeRefArg(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kTypeRef) {
    CheckTypeRefArgInner(expr->lhs, expr->range.start);
  }
  WalkExprForTypeRefArg(expr->lhs);
  WalkExprForTypeRefArg(expr->rhs);
  WalkExprForTypeRefArg(expr->condition);
  WalkExprForTypeRefArg(expr->true_expr);
  WalkExprForTypeRefArg(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefArg(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefArg(arg);
}

void Elaborator::WalkStmtsForTypeRefArg(const Stmt* s) {
  if (!s) return;
  WalkExprForTypeRefArg(s->lhs);
  WalkExprForTypeRefArg(s->rhs);
  WalkExprForTypeRefArg(s->expr);
  WalkExprForTypeRefArg(s->condition);
  WalkExprForTypeRefArg(s->assert_expr);
  if (s->var_decl_type.type_ref_expr) {
    CheckTypeRefArgInner(s->var_decl_type.type_ref_expr, s->range.start);
  }
  for (auto* sub : s->stmts) WalkStmtsForTypeRefArg(sub);
  WalkStmtsForTypeRefArg(s->then_branch);
  WalkStmtsForTypeRefArg(s->else_branch);
  WalkStmtsForTypeRefArg(s->body);
  WalkStmtsForTypeRefArg(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForTypeRefArg(ci.body);
}

void Elaborator::ValidateTypeRefArgs(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->data_type.type_ref_expr) {
      CheckTypeRefArgInner(item->data_type.type_ref_expr, item->loc);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForTypeRefArg(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForTypeRefArg(item->assign_rhs);
    }
  }
}

// After the tagged keyword the BNF allows only a member identifier drawn from
// the target tagged union type. When the LHS of an assignment resolves to a
// variable whose typedef is a tagged union, reject a tag name that is not
// declared in that union.
void Elaborator::CheckTaggedExprMember(const Expr* lhs, const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (rhs->kind != ExprKind::kTagged) return;
  if (!rhs->rhs || rhs->rhs->kind != ExprKind::kIdentifier) return;
  if (lhs->kind != ExprKind::kIdentifier) return;

  auto vit = var_named_types_.find(lhs->text);
  if (vit == var_named_types_.end()) return;

  auto tit = typedefs_.find(vit->second);
  if (tit == typedefs_.end()) return;

  const auto& dt = tit->second;
  if (dt.kind != DataTypeKind::kUnion || !dt.is_tagged) return;

  auto tag_name = rhs->rhs->text;
  for (const auto& m : dt.struct_members) {
    if (m.name == tag_name) return;
  }

  diag_.Error(rhs->range.start,
              std::format("tagged union '{}' has no member named '{}'",
                          vit->second, tag_name));
}

void Elaborator::WalkStmtsForTaggedExpr(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    CheckTaggedExprMember(s->lhs, s->rhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForTaggedExpr(sub);
  WalkStmtsForTaggedExpr(s->then_branch);
  WalkStmtsForTaggedExpr(s->else_branch);
  WalkStmtsForTaggedExpr(s->body);
  WalkStmtsForTaggedExpr(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForTaggedExpr(ci.body);
}

void Elaborator::ValidateTaggedUnionMembers(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForTaggedExpr(item->body);
    }
  }
}

static bool IsRealVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && IsRealType(it->second);
}

static bool IsIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:

    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:

    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:

    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:

    case TokenKind::kPercent:
      return true;
    default:
      return false;
  }
}

static bool IsUnaryIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForRealOps(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool lhs_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    bool rhs_real = expr->rhs && IsRealVar(expr->rhs, var_types_);
    if ((lhs_real || rhs_real) && IsIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  if (expr->kind == ExprKind::kUnary) {
    bool operand_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    if (operand_real && IsUnaryIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  WalkExprForRealOps(expr->lhs);
  WalkExprForRealOps(expr->rhs);
  WalkExprForRealOps(expr->condition);
  WalkExprForRealOps(expr->true_expr);
  WalkExprForRealOps(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForRealOps(elem);
  for (auto* arg : expr->args) WalkExprForRealOps(arg);
}

void Elaborator::WalkStmtsForRealOps(const Stmt* s) {
  if (!s) return;
  WalkExprForRealOps(s->rhs);
  WalkExprForRealOps(s->lhs);
  WalkExprForRealOps(s->expr);
  WalkExprForRealOps(s->condition);
  WalkExprForRealOps(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForRealOps(sub);
  WalkStmtsForRealOps(s->then_branch);
  WalkStmtsForRealOps(s->else_branch);
  WalkStmtsForRealOps(s->body);
  WalkStmtsForRealOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForRealOps(ci.body);
}

void Elaborator::ValidateRealOperatorRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForRealOps(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForRealOps(item->assign_rhs);
    }
  }
}

static bool IsAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kEq:
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForAssignInExpr(const Expr* expr,
                                         bool in_event_or_cont) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary && IsAssignOp(expr->op)) {
    if (in_event_or_cont) {
      diag_.Error(expr->range.start,
                  "assignment operator within expression is illegal in "
                  "this context");
    }
  }
  WalkExprForAssignInExpr(expr->lhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->rhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->condition, in_event_or_cont);
  WalkExprForAssignInExpr(expr->true_expr, in_event_or_cont);
  WalkExprForAssignInExpr(expr->false_expr, in_event_or_cont);
  for (auto* elem : expr->elements)
    WalkExprForAssignInExpr(elem, in_event_or_cont);
  for (auto* arg : expr->args) WalkExprForAssignInExpr(arg, in_event_or_cont);
}

void Elaborator::WalkStmtsForAssignInExpr(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kAssign && s->rhs) {
    WalkExprForAssignInExpr(s->rhs, true);
  }
  for (auto* sub : s->stmts) WalkStmtsForAssignInExpr(sub);
  WalkStmtsForAssignInExpr(s->then_branch);
  WalkStmtsForAssignInExpr(s->else_branch);
  WalkStmtsForAssignInExpr(s->body);
  WalkStmtsForAssignInExpr(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssignInExpr(ci.body);
}

void Elaborator::ValidateAssignInExprRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      for (const auto& ev : item->sensitivity) {
        WalkExprForAssignInExpr(ev.signal, true);
      }
      if (item->body) WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kInitialBlock && item->body) {
      WalkStmtsForAssignInExpr(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAssignInExpr(item->assign_rhs, true);
    }
  }
}

static std::string_view AliasNetIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

static bool ExprContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (ExprContainsHierarchicalRef(e->lhs)) return true;
  if (ExprContainsHierarchicalRef(e->rhs)) return true;
  if (ExprContainsHierarchicalRef(e->base)) return true;
  for (auto* elem : e->elements) {
    if (ExprContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

namespace {

void CheckAliasSelfAlias(const ModuleItem* item, DiagEngine& diag) {
  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag.Error(item->loc, std::format("net '{}' aliased to itself", name));
    }
  }
}

void CheckAliasOperandKinds(
    const ModuleItem* item, DiagEngine& diag,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& declared_names) {
  for (auto* net : item->alias_nets) {
    if (ExprContainsHierarchicalRef(net)) {
      diag.Error(item->loc,
                 "hierarchical references cannot be used in alias statements");
    }
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!net_names.count(name) && declared_names.count(name)) {
      diag.Error(item->loc,
                 std::format("'{}' is a variable, not a net; "
                             "variables cannot appear in alias statements",
                             name));
    }
  }
}

std::vector<std::string_view> CollectAliasNetNames(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& net_names) {
  std::vector<std::string_view> ident_names;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (!name.empty() && net_names.count(name)) ident_names.push_back(name);
  }
  return ident_names;
}

void CheckAliasNetTypeCompat(
    const ModuleItem* item, DiagEngine& diag,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const std::vector<std::string_view>& ident_names) {
  if (ident_names.size() < 2) return;
  auto first_type_it = var_types.find(ident_names[0]);
  NetType first_net_type = NetType::kWire;
  if (first_type_it != var_types.end())
    first_net_type = DataTypeToNetType(first_type_it->second);
  for (size_t i = 1; i < ident_names.size(); ++i) {
    NetType cur_net_type = NetType::kWire;
    auto cur_type_it = var_types.find(ident_names[i]);
    if (cur_type_it != var_types.end())
      cur_net_type = DataTypeToNetType(cur_type_it->second);
    if (cur_net_type != first_net_type) {
      diag.Error(item->loc,
                 std::format("nets in alias statement have incompatible types; "
                             "'{}' and '{}' are different net types",
                             ident_names[0], ident_names[i]));
      break;
    }
  }
}

template <typename ScopeFn>
void CheckAliasNetWidthCompat(const ModuleItem* item, DiagEngine& diag,
                              RtlirModule* mod,
                              const std::vector<std::string_view>& ident_names,
                              ScopeFn scope) {
  if (ident_names.size() < 2) return;
  auto scoped_first = scope(ident_names[0]);
  uint32_t first_width = 0;
  for (const auto& n : mod->nets) {
    if (n.name == scoped_first) {
      first_width = n.width;
      break;
    }
  }
  for (size_t i = 1; i < ident_names.size(); ++i) {
    auto scoped = scope(ident_names[i]);
    uint32_t w = 0;
    for (const auto& n : mod->nets) {
      if (n.name == scoped) {
        w = n.width;
        break;
      }
    }
    if (w != first_width) {
      diag.Error(item->loc,
                 std::format("nets in alias statement have different widths; "
                             "'{}' has width {} but '{}' has width {}",
                             ident_names[0], first_width, ident_names[i], w));
      break;
    }
  }
}

void CheckAliasDuplicatePairs(
    const ModuleItem* item, DiagEngine& diag,
    std::set<std::pair<std::string_view, std::string_view>>& alias_pairs,
    const std::vector<std::string_view>& ident_names) {
  for (size_t i = 0; i < ident_names.size(); ++i) {
    for (size_t j = i + 1; j < ident_names.size(); ++j) {
      auto a = ident_names[i];
      auto b = ident_names[j];
      auto pair = (a < b) ? std::make_pair(a, b) : std::make_pair(b, a);
      if (!alias_pairs.insert(pair).second) {
        diag.Error(item->loc, std::format("alias between '{}' and '{}' "
                                          "specified more than once",
                                          a, b));
      }
    }
  }
}

}  // namespace

void Elaborator::ValidateAlias(const ModuleItem* item, RtlirModule* mod) {
  CheckAliasSelfAlias(item, diag_);
  CheckAliasOperandKinds(item, diag_, net_names_, declared_names_);
  std::vector<std::string_view> ident_names =
      CollectAliasNetNames(item, net_names_);
  CheckAliasNetTypeCompat(item, diag_, var_types_, ident_names);
  CheckAliasNetWidthCompat(
      item, diag_, mod, ident_names,
      [this](std::string_view n) { return ScopedName(n); });
  CheckAliasDuplicatePairs(item, diag_, alias_pairs_, ident_names);
}

void Elaborator::CheckAssocConcatTargetInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_assoc) return;
  diag_.Error(
      s->rhs->range.start,
      "unpacked array concatenation cannot target an associative array");
}

void Elaborator::WalkStmtsForAssocConcatTarget(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckAssocConcatTargetInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForAssocConcatTarget(sub);
  WalkStmtsForAssocConcatTarget(s->then_branch);
  WalkStmtsForAssocConcatTarget(s->else_branch);
  WalkStmtsForAssocConcatTarget(s->body);
  WalkStmtsForAssocConcatTarget(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssocConcatTarget(ci.body);
}

void Elaborator::ValidateAssocConcatTarget(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForAssocConcatTarget(item->body);
    }
  }
}

}  // namespace delta
