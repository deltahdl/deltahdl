#include <charconv>
#include <format>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
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

void Elaborator::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  auto l_name = AggregateOperandName(expr->lhs);
  auto r_name = AggregateOperandName(expr->rhs);
  if (l_name.empty() || r_name.empty()) return;
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

bool Elaborator::TypeRefArgUsesDynamicElement(const Expr* e) const {
  if (!e) return false;
  if (e->kind == ExprKind::kSelect && e->base &&
      e->base->kind == ExprKind::kIdentifier) {
    auto it = var_array_info_.find(e->base->text);
    if (it != var_array_info_.end() &&
        (it->second.is_dynamic || it->second.is_assoc)) {
      return true;
    }
  }
  if (TypeRefArgUsesDynamicElement(e->lhs)) return true;
  if (TypeRefArgUsesDynamicElement(e->rhs)) return true;
  if (TypeRefArgUsesDynamicElement(e->base)) return true;
  if (TypeRefArgUsesDynamicElement(e->index)) return true;
  if (TypeRefArgUsesDynamicElement(e->condition)) return true;
  if (TypeRefArgUsesDynamicElement(e->true_expr)) return true;
  if (TypeRefArgUsesDynamicElement(e->false_expr)) return true;
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

static NetType DataTypeKindToNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kTri: return NetType::kTri;
    case DataTypeKind::kWand: return NetType::kWand;
    case DataTypeKind::kWor: return NetType::kWor;
    case DataTypeKind::kTriand: return NetType::kTriand;
    case DataTypeKind::kTrior: return NetType::kTrior;
    case DataTypeKind::kTri0: return NetType::kTri0;
    case DataTypeKind::kTri1: return NetType::kTri1;
    case DataTypeKind::kSupply0: return NetType::kSupply0;
    case DataTypeKind::kSupply1: return NetType::kSupply1;
    case DataTypeKind::kTrireg: return NetType::kTrireg;
    case DataTypeKind::kUwire: return NetType::kUwire;
    default: return NetType::kWire;
  }
}

void Elaborator::ValidateAlias(const ModuleItem* item, RtlirModule* mod) {

  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag_.Error(item->loc, std::format("net '{}' aliased to itself", name));
    }
  }

  for (auto* net : item->alias_nets) {
    if (ExprContainsHierarchicalRef(net)) {
      diag_.Error(item->loc,
                  "hierarchical references cannot be used in alias statements");
    }
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!net_names_.count(name) && declared_names_.count(name)) {
      diag_.Error(item->loc,
                  std::format("'{}' is a variable, not a net; "
                              "variables cannot appear in alias statements",
                              name));
    }
  }

  std::vector<std::string_view> ident_names;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (!name.empty() && net_names_.count(name)) ident_names.push_back(name);
  }
  if (ident_names.size() >= 2) {
    auto first_type_it = var_types_.find(ident_names[0]);
    NetType first_net_type = NetType::kWire;
    if (first_type_it != var_types_.end())
      first_net_type = DataTypeKindToNetType(first_type_it->second);
    for (size_t i = 1; i < ident_names.size(); ++i) {
      NetType cur_net_type = NetType::kWire;
      auto cur_type_it = var_types_.find(ident_names[i]);
      if (cur_type_it != var_types_.end())
        cur_net_type = DataTypeKindToNetType(cur_type_it->second);
      if (cur_net_type != first_net_type) {
        diag_.Error(
            item->loc,
            std::format(
                "nets in alias statement have incompatible types; "
                "'{}' and '{}' are different net types",
                ident_names[0], ident_names[i]));
        break;
      }
    }
  }

  if (ident_names.size() >= 2) {
    auto scoped_first = ScopedName(ident_names[0]);
    uint32_t first_width = 0;
    for (const auto& n : mod->nets) {
      if (n.name == scoped_first) { first_width = n.width; break; }
    }
    for (size_t i = 1; i < ident_names.size(); ++i) {
      auto scoped = ScopedName(ident_names[i]);
      uint32_t w = 0;
      for (const auto& n : mod->nets) {
        if (n.name == scoped) { w = n.width; break; }
      }
      if (w != first_width) {
        diag_.Error(
            item->loc,
            std::format(
                "nets in alias statement have different widths; "
                "'{}' has width {} but '{}' has width {}",
                ident_names[0], first_width, ident_names[i], w));
        break;
      }
    }
  }

  for (size_t i = 0; i < ident_names.size(); ++i) {
    for (size_t j = i + 1; j < ident_names.size(); ++j) {
      auto a = ident_names[i];
      auto b = ident_names[j];
      auto pair = (a < b) ? std::make_pair(a, b) : std::make_pair(b, a);
      if (!alias_pairs_.insert(pair).second) {
        diag_.Error(item->loc,
                    std::format("alias between '{}' and '{}' "
                                "specified more than once",
                                a, b));
      }
    }
  }
}

void Elaborator::CheckAssocConcatTargetInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_assoc) return;
  diag_.Error(s->rhs->range.start,
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
        if (inner->kind == ExprKind::kIdentifier &&
            var_array_info_.count(inner->text)) {
          diag_.Error(inner->range.start,
                      "array-typed identifier in assignment pattern targeting "
                      "unpacked array");
        }
      }
    } else if (elem->kind == ExprKind::kIdentifier &&
               var_array_info_.count(elem->text)) {
      diag_.Error(elem->range.start,
                  "array-typed identifier in assignment pattern targeting "
                  "unpacked array");
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

void Elaborator::WalkExprForUnsizedInConcat(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kConcatenation) {
    for (auto* elem : expr->elements) {
      if (elem->kind == ExprKind::kIntegerLiteral) {
        auto tick = elem->text.find('\'');
        if (tick == std::string_view::npos || tick == 0) {
          diag_.Error(elem->range.start,
                      "unsized constant is not allowed in a concatenation");
        }
      }
    }
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

  bool is_array_concat_rhs =
      s->rhs && s->rhs->kind == ExprKind::kConcatenation &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      (s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      var_array_info_.count(s->lhs->text);
  if (is_array_concat_rhs) {
    for (auto* elem : s->rhs->elements)
      WalkExprForUnsizedInConcat(elem);
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
    if (item->init_value) {
      WalkExprForUnsizedInConcat(item->init_value);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.init_value);
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
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
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
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
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

void Elaborator::WalkExprForReplicateMultiplier(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kReplicate) {
    const Expr* rc = expr->repeat_count;
    if (RepeatCountHasXZ(rc)) {
      diag_.Error(rc->range.start,
                  "replication multiplier shall not contain x or z");
    } else {
      auto val = ConstEvalInt(rc);
      if (val) {
        if (*val < 0) {
          diag_.Error(rc->range.start,
                      "replication multiplier shall not be negative");
        } else if (*val == 0) {

        }
      }
    }
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

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         DiagEngine& diag) {
  if (!expr) return;
  if (IsZeroReplicate(expr)) {
    diag.Error(expr->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size");
  }
  if (expr->kind == ExprKind::kConcatenation) {

    bool all_zero = true;
    for (const auto* elem : expr->elements) {
      if (!IsZeroReplicate(elem)) {
        all_zero = false;
        break;
      }
    }
    if (all_zero && !expr->elements.empty()) {
      diag.Error(expr->range.start,
                 "zero replication shall appear only within a concatenation "
                 "in which at least one operand has a positive size");
    }

    for (const auto* elem : expr->elements) {
      if (!IsZeroReplicate(elem)) {
        CheckZeroReplicateStandalone(elem, diag);
      }
    }
    return;
  }
  CheckZeroReplicateStandalone(expr->lhs, diag);
  CheckZeroReplicateStandalone(expr->rhs, diag);
  CheckZeroReplicateStandalone(expr->condition, diag);
  CheckZeroReplicateStandalone(expr->true_expr, diag);
  CheckZeroReplicateStandalone(expr->false_expr, diag);
  for (const auto* elem : expr->elements)
    CheckZeroReplicateStandalone(elem, diag);
  for (const auto* arg : expr->args)
    CheckZeroReplicateStandalone(arg, diag);
}

static void WalkStmtsForZeroReplicateStandalone(const Stmt* s,
                                                DiagEngine& diag) {
  if (!s) return;
  CheckZeroReplicateStandalone(s->rhs, diag);
  CheckZeroReplicateStandalone(s->lhs, diag);
  CheckZeroReplicateStandalone(s->expr, diag);
  CheckZeroReplicateStandalone(s->condition, diag);
  CheckZeroReplicateStandalone(s->assert_expr, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForZeroReplicateStandalone(sub, diag);
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
    if (item->init_value) {
      WalkExprForReplicateMultiplier(item->init_value);
      CheckZeroReplicateStandalone(item->init_value, diag_);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForReplicateMultiplier(p.init_value);
    CheckZeroReplicateStandalone(p.init_value, diag_);
  }
}

bool Elaborator::ConcatContainsStringElement(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    auto it = var_types_.find(expr->text);
    return it != var_types_.end() && it->second == DataTypeKind::kString;
  }
  if (expr->kind == ExprKind::kStringLiteral) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ConcatContainsStringElement(elem)) return true;
    }
  }
  return false;
}

void Elaborator::CheckStringConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (lhs->kind != ExprKind::kConcatenation) return;
  if (ConcatContainsStringElement(lhs)) {
    diag_.Error(lhs->range.start,
                "string concatenation is not allowed on the left-hand side "
                "of an assignment");
  }
}

void Elaborator::WalkStmtsForStringConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckStringConcatLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForStringConcatLvalue(sub);
  WalkStmtsForStringConcatLvalue(s->then_branch);
  WalkStmtsForStringConcatLvalue(s->else_branch);
  WalkStmtsForStringConcatLvalue(s->body);
  WalkStmtsForStringConcatLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForStringConcatLvalue(ci.body);
}

void Elaborator::ValidateStringConcatLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForStringConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringConcatLvalue(item->assign_lhs);
    }
  }
}

static bool ClassHasHiddenMember(const ClassDecl* cls);

void Elaborator::WalkExprForStreamingContext(const Expr* expr,
                                             bool is_valid_context) {
  if (!expr) return;
  if (expr->kind == ExprKind::kStreamingConcat) {
    if (!is_valid_context) {
      diag_.Error(expr->range.start,
                  "streaming concatenation shall not be used as an operand "
                  "of an expression other than an assignment or bit-stream "
                  "cast");
    }

    for (auto* elem : expr->elements) {
      // §11.4.14.1: when a non-null class handle is streamed, its data members
      // are packed in turn. Streaming a handle whose class exposes local or
      // protected members is illegal unless those members are accessible at
      // the streaming operator, approximated here (as in the bit-stream cast
      // rule of §6.24.3) by allowing only the current instance `this`.
      if (elem && elem->kind == ExprKind::kIdentifier &&
          elem->text != "this") {
        auto it = class_var_types_.find(elem->text);
        if (it != class_var_types_.end() &&
            ClassHasHiddenMember(FindClassDecl(it->second, unit_))) {
          diag_.Error(elem->range.start,
                      std::format("class handle '{}' is illegal as a streaming "
                                  "concatenation operand: its class has local "
                                  "or protected members",
                                  elem->text));
        }
      }
      // §11.4.14.1: an operand that is none of a bit-stream type, an unpacked
      // array, a struct, an untagged union, or a class handle cannot be packed
      // into the stream; such an operand is skipped and an error is issued. The
      // statically recognizable non-bit-stream scalar types are the real
      // family, event, chandle, and virtual interface.
      if (elem && elem->kind == ExprKind::kIdentifier) {
        auto vt = var_types_.find(elem->text);
        if (vt != var_types_.end()) {
          auto k = vt->second;
          if (IsRealType(k) || k == DataTypeKind::kEvent ||
              k == DataTypeKind::kChandle ||
              k == DataTypeKind::kVirtualInterface) {
            diag_.Error(elem->range.start,
                        std::format("'{}' is not a bit-stream type and cannot "
                                    "be a streaming concatenation operand",
                                    elem->text));
          }
        }
      }
      WalkExprForStreamingContext(elem, true);
    }

    // §11.4.14.2: a slice_size written as a constant integral expression names
    // the block width used to re-order the generic stream, so its value must be
    // positive; a zero or negative slice size is illegal. A slice_size given as
    // a simple type instead names a block width equal to that type's size,
    // which is inherently positive and therefore exempt from this check. The
    // parser records a bare numeric slice_size as an identifier carrying the
    // literal text, while a non-numeric identifier names a type.
    if (const Expr* slice = expr->lhs) {
      std::optional<int64_t> value;
      if (slice->kind == ExprKind::kIdentifier) {
        int64_t parsed = 0;
        const char* begin = slice->text.data();
        const char* end = begin + slice->text.size();
        auto [ptr, ec] = std::from_chars(begin, end, parsed);
        if (ec == std::errc() && ptr == end) value = parsed;
      } else {
        value = ConstEvalInt(slice);
      }
      if (value && *value <= 0) {
        diag_.Error(slice->range.start,
                    "streaming slice_size shall be a positive constant");
      }
    }

    WalkExprForStreamingContext(expr->lhs, false);
    return;
  }
  if (expr->kind == ExprKind::kCast) {

    WalkExprForStreamingContext(expr->lhs, true);
    return;
  }

  WalkExprForStreamingContext(expr->lhs, false);
  WalkExprForStreamingContext(expr->rhs, false);
  WalkExprForStreamingContext(expr->condition, false);
  WalkExprForStreamingContext(expr->true_expr, false);
  WalkExprForStreamingContext(expr->false_expr, false);
  for (auto* elem : expr->elements) WalkExprForStreamingContext(elem, false);
  for (auto* arg : expr->args) WalkExprForStreamingContext(arg, false);
}

// §11.4.14: a streaming_concatenation used as the source of an assignment
// requires a target that is either another streaming_concatenation or a data
// object of bit-stream type. Reject the obviously-non-bit-stream targets we
// can recognise from the variable-type map (real family, event, chandle,
// virtual interface). Targets we cannot type-check from a simple identifier
// (selects, member accesses) are left to type-aware downstream checks.
void Elaborator::CheckStreamingSourceTargetType(const Expr* lhs,
                                                const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (rhs->kind != ExprKind::kStreamingConcat) return;
  if (lhs->kind == ExprKind::kStreamingConcat) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types_.find(lhs->text);
  if (it == var_types_.end()) return;
  auto k = it->second;
  bool not_bitstream = IsRealType(k) || k == DataTypeKind::kEvent ||
                       k == DataTypeKind::kChandle ||
                       k == DataTypeKind::kVirtualInterface;
  if (not_bitstream) {
    diag_.Error(lhs->range.start,
                "target of a streaming concatenation source assignment must "
                "be a bit-stream type");
  }
}

void Elaborator::WalkStmtsForStreamingContext(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign ||
      s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {

    WalkExprForStreamingContext(s->lhs, true);
    WalkExprForStreamingContext(s->rhs, true);
    CheckStreamingSourceTargetType(s->lhs, s->rhs);
  } else {

    WalkExprForStreamingContext(s->lhs, false);
    WalkExprForStreamingContext(s->rhs, false);
  }
  WalkExprForStreamingContext(s->expr, false);
  WalkExprForStreamingContext(s->condition, false);
  WalkExprForStreamingContext(s->assert_expr, false);
  for (auto* sub : s->stmts) WalkStmtsForStreamingContext(sub);
  WalkStmtsForStreamingContext(s->then_branch);
  WalkStmtsForStreamingContext(s->else_branch);
  WalkStmtsForStreamingContext(s->body);
  WalkStmtsForStreamingContext(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForStreamingContext(ci.body);
}

void Elaborator::ValidateStreamingConcatContext(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForStreamingContext(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForStreamingContext(item->assign_lhs, true);
      WalkExprForStreamingContext(item->assign_rhs, true);
      CheckStreamingSourceTargetType(item->assign_lhs, item->assign_rhs);
    }
  }
}

// §6.24.3: a class is illegal as a bit-stream-cast source when it exposes any
// local or protected member, except when the source handle is the keyword
// `this` (the current instance retains private access).
static bool ClassHasHiddenMember(const ClassDecl* cls) {
  if (!cls) return false;
  for (const auto* m : cls->members) {
    if (m && (m->is_local || m->is_protected)) return true;
  }
  return false;
}

static uint32_t CastTargetSimpleWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "int" || t == "integer") return 32;
  if (t == "longint") return 64;
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  return 0;
}

void Elaborator::CheckBitStreamCastExpr(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCast) return;
  auto target = expr->text;
  if (target.empty()) return;

  // §6.24.3: an associative array type shall be illegal as a destination type
  // for a bit-stream cast.
  if (assoc_typedef_names_.count(target) > 0) {
    diag_.Error(expr->range.start,
                std::format("associative array type '{}' is illegal as a "
                            "bit-stream cast destination",
                            target));
    return;
  }

  // §6.24.3: a class handle whose class exposes local or protected members
  // shall be illegal as a source type, except when the handle is the current
  // instance `this`. The rule applies to a bit-stream cast, i.e., when the
  // destination is not itself a class type.
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->lhs->text != "this" && class_names_.count(target) == 0) {
    auto it = class_var_types_.find(expr->lhs->text);
    if (it != class_var_types_.end()) {
      const auto* cls = FindClassDecl(it->second, unit_);
      if (ClassHasHiddenMember(cls)) {
        diag_.Error(expr->range.start,
                    std::format("class handle '{}' is illegal as a bit-stream "
                                "cast source: its class has local or "
                                "protected members",
                                expr->lhs->text));
        return;
      }
    }
  }

  // §6.24.3: when both source and destination are fixed-size types of
  // different sizes and either is unpacked, the cast generates a compile-time
  // error. Two paths are checked: the operand is an unpacked-array variable,
  // or the destination is an unpacked-array typedef. Dynamic-size cases are
  // left to the simulator since their sizes are not known until runtime.
  if (!expr->lhs) return;

  auto dst_unpacked_it = fixed_unpacked_typedef_widths_.find(target);
  if (dst_unpacked_it != fixed_unpacked_typedef_widths_.end()) {
    uint32_t src_width = InferExprWidth(expr->lhs, typedefs_);
    if (src_width > 0 && src_width != dst_unpacked_it->second) {
      diag_.Error(expr->range.start,
                  std::format("bit-stream cast between fixed-size types of "
                              "different sizes ({} bits to {} bits) with an "
                              "unpacked destination is illegal",
                              src_width, dst_unpacked_it->second));
      return;
    }
  }

  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  auto src_name = expr->lhs->text;
  auto var_it = var_array_info_.find(src_name);
  if (var_it == var_array_info_.end()) return;
  const auto& info = var_it->second;
  if (info.is_dynamic || info.is_assoc) return;
  if (info.unpacked_size == 0 || info.elem_width == 0) return;
  uint32_t src_width = info.unpacked_size * info.elem_width;

  uint32_t dst_width = CastTargetSimpleWidth(target);
  if (dst_width == 0) {
    auto td = typedefs_.find(target);
    if (td != typedefs_.end()) dst_width = EvalTypeWidth(td->second, typedefs_);
  }
  if (dst_width == 0) return;
  if (src_width == dst_width) return;
  diag_.Error(expr->range.start,
              std::format("bit-stream cast between fixed-size types of "
                          "different sizes ({} bits to {} bits) with an "
                          "unpacked operand is illegal",
                          src_width, dst_width));
}

void Elaborator::WalkExprForBitStreamCast(const Expr* expr) {
  if (!expr) return;
  CheckBitStreamCastExpr(expr);
  WalkExprForBitStreamCast(expr->lhs);
  WalkExprForBitStreamCast(expr->rhs);
  WalkExprForBitStreamCast(expr->base);
  WalkExprForBitStreamCast(expr->index);
  WalkExprForBitStreamCast(expr->index_end);
  WalkExprForBitStreamCast(expr->condition);
  WalkExprForBitStreamCast(expr->true_expr);
  WalkExprForBitStreamCast(expr->false_expr);
  for (const auto* elem : expr->elements) WalkExprForBitStreamCast(elem);
  for (const auto* arg : expr->args) WalkExprForBitStreamCast(arg);
}

void Elaborator::WalkStmtsForBitStreamCast(const Stmt* s) {
  if (!s) return;
  WalkExprForBitStreamCast(s->lhs);
  WalkExprForBitStreamCast(s->rhs);
  WalkExprForBitStreamCast(s->expr);
  WalkExprForBitStreamCast(s->condition);
  for (auto* sub : s->stmts) WalkStmtsForBitStreamCast(sub);
  WalkStmtsForBitStreamCast(s->then_branch);
  WalkStmtsForBitStreamCast(s->else_branch);
  WalkStmtsForBitStreamCast(s->body);
  WalkStmtsForBitStreamCast(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForBitStreamCast(ci.body);
}

void Elaborator::ValidateBitStreamCast(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForBitStreamCast(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForBitStreamCast(item->assign_lhs);
      WalkExprForBitStreamCast(item->assign_rhs);
    }
    if (item->kind == ModuleItemKind::kVarDecl) {
      WalkExprForBitStreamCast(item->init_expr);
    }
  }
}

static std::string_view HierRefLeftmost(const Expr* e) {
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return HierRefLeftmost(e->lhs);
  return {};
}

static bool ExprRefersToChecker(
    const Expr* e,
    const std::unordered_set<std::string_view>& checker_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && checker_names.count(leftmost)) return true;
  }
  if (ExprRefersToChecker(e->lhs, checker_names)) return true;
  if (ExprRefersToChecker(e->rhs, checker_names)) return true;
  if (ExprRefersToChecker(e->base, checker_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToChecker(elem, checker_names)) return true;
  }
  return false;
}

static void WalkStmtsForCheckerRef(
    const Stmt* s,
    const std::unordered_set<std::string_view>& checker_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToChecker(s->lhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted");
  if (s->rhs && ExprRefersToChecker(s->rhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted");
  for (auto* child : s->children)
    WalkStmtsForCheckerRef(child, checker_names, diag);
  if (s->if_body) WalkStmtsForCheckerRef(s->if_body, checker_names, diag);
  if (s->else_body) WalkStmtsForCheckerRef(s->else_body, checker_names, diag);
}

void Elaborator::ValidateHierRefIntoChecker(const ModuleDecl* decl) {
  if (checker_inst_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToChecker(item->assign_lhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted");
      if (ExprRefersToChecker(item->assign_rhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForCheckerRef(item->body, checker_inst_names_, diag_);
  }
}

static bool ExprRefersToProgram(
    const Expr* e,
    const std::unordered_set<std::string_view>& program_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && program_names.count(leftmost)) return true;
  }
  if (ExprRefersToProgram(e->lhs, program_names)) return true;
  if (ExprRefersToProgram(e->rhs, program_names)) return true;
  if (ExprRefersToProgram(e->base, program_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToProgram(elem, program_names)) return true;
  }
  return false;
}

static void WalkStmtsForProgramRef(
    const Stmt* s,
    const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToProgram(s->lhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted");
  if (s->rhs && ExprRefersToProgram(s->rhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted");
  for (auto* child : s->children)
    WalkStmtsForProgramRef(child, program_names, diag);
  if (s->if_body) WalkStmtsForProgramRef(s->if_body, program_names, diag);
  if (s->else_body) WalkStmtsForProgramRef(s->else_body, program_names, diag);
}

void Elaborator::ValidateHierRefIntoProgram(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToProgram(item->assign_lhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted");
      if (ExprRefersToProgram(item->assign_rhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body)
      WalkStmtsForProgramRef(item->body, program_inst_names_, diag_);
  }
}

void Elaborator::ValidateAnonymousProgramHierRefs() {
  std::unordered_set<std::string_view> program_names;
  for (const auto* p : unit_->programs) {
    if (!p->name.empty()) program_names.insert(p->name);
  }
  if (program_names.empty()) return;
  for (const auto* item : unit_->cu_items) {
    if (!item->from_anonymous_program) continue;
    if (item->body) WalkStmtsForProgramRef(item->body, program_names, diag_);
  }
}

static void CollectHierPathComponents(const Expr* e,
                                      std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectHierPathComponents(e->lhs, out);
    CollectHierPathComponents(e->rhs, out);
  }
}

static bool ExprRefersToAutomatic(
    const Expr* e,
    const std::unordered_set<std::string_view>& auto_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    std::vector<std::string_view> components;
    CollectHierPathComponents(e, components);
    for (size_t i = 0; i + 1 < components.size(); ++i) {
      if (auto_names.count(components[i])) return true;
    }
  }
  if (ExprRefersToAutomatic(e->lhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->rhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->base, auto_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToAutomatic(elem, auto_names)) return true;
  }
  return false;
}

static void WalkStmtsForAutoRef(
    const Stmt* s,
    const std::unordered_set<std::string_view>& auto_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToAutomatic(s->lhs, auto_names))
    diag.Error(s->range.start,
               "hierarchical reference to object in automatic task or "
               "function is not permitted");
  if (s->rhs && ExprRefersToAutomatic(s->rhs, auto_names))
    diag.Error(s->range.start,
               "hierarchical reference to object in automatic task or "
               "function is not permitted");
  for (auto* child : s->children)
    WalkStmtsForAutoRef(child, auto_names, diag);
  if (s->if_body) WalkStmtsForAutoRef(s->if_body, auto_names, diag);
  if (s->else_body) WalkStmtsForAutoRef(s->else_body, auto_names, diag);
}

void Elaborator::ValidateHierRefToAutomatic(const ModuleDecl* decl) {
  if (auto_task_func_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToAutomatic(item->assign_lhs, auto_task_func_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to object in automatic task or "
                    "function is not permitted");
      if (ExprRefersToAutomatic(item->assign_rhs, auto_task_func_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to object in automatic task or "
                    "function is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForAutoRef(item->body, auto_task_func_names_, diag_);
  }
}

static bool IsProgramSubroutineCallExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& program_names) {
  if (!e || e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  auto leftmost = HierRefLeftmost(callee);
  return !leftmost.empty() && program_names.count(leftmost) > 0;
}

static void WalkExprForProgramCall(
    const Expr* e,
    const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag, SourceLoc loc) {
  if (!e) return;
  if (IsProgramSubroutineCallExpr(e, program_names)) {
    diag.Error(loc,
               "calling a program subroutine from within a design module is "
               "not permitted");
  }
  WalkExprForProgramCall(e->lhs, program_names, diag, loc);
  WalkExprForProgramCall(e->rhs, program_names, diag, loc);
  WalkExprForProgramCall(e->condition, program_names, diag, loc);
  WalkExprForProgramCall(e->true_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->false_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->base, program_names, diag, loc);
  WalkExprForProgramCall(e->index, program_names, diag, loc);
  WalkExprForProgramCall(e->index_end, program_names, diag, loc);
  WalkExprForProgramCall(e->with_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->repeat_count, program_names, diag, loc);
  for (auto* arg : e->args)
    WalkExprForProgramCall(arg, program_names, diag, loc);
  for (auto* elem : e->elements)
    WalkExprForProgramCall(elem, program_names, diag, loc);
}

static void WalkStmtForProgramCall(
    const Stmt* s,
    const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  auto loc = s->range.start;
  WalkExprForProgramCall(s->lhs, program_names, diag, loc);
  WalkExprForProgramCall(s->rhs, program_names, diag, loc);
  WalkExprForProgramCall(s->expr, program_names, diag, loc);
  WalkExprForProgramCall(s->condition, program_names, diag, loc);
  for (auto* sub : s->stmts)
    WalkStmtForProgramCall(sub, program_names, diag);
  WalkStmtForProgramCall(s->then_branch, program_names, diag);
  WalkStmtForProgramCall(s->else_branch, program_names, diag);
  WalkStmtForProgramCall(s->body, program_names, diag);
  WalkStmtForProgramCall(s->for_body, program_names, diag);
  for (auto* init : s->for_inits)
    WalkStmtForProgramCall(init, program_names, diag);
  for (auto* step : s->for_steps)
    WalkStmtForProgramCall(step, program_names, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtForProgramCall(fs, program_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtForProgramCall(ci.body, program_names, diag);
}

void Elaborator::ValidateProgramSubroutineCall(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForProgramCall(item->assign_lhs, program_inst_names_, diag_,
                             item->loc);
      WalkExprForProgramCall(item->assign_rhs, program_inst_names_, diag_,
                             item->loc);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body)
      WalkStmtForProgramCall(item->body, program_inst_names_, diag_);
  }
}

}
