#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateEdgeOnReal(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kNone) continue;
    auto name = ExprIdent(ev.signal);
    if (name.empty()) continue;
    auto it = var_types_.find(name);
    if (it != var_types_.end() && IsRealType(it->second)) {
      diag_.Error(item->loc, "edge event on real type is illegal");
    }
  }
}

static bool IsChandleVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kChandle;
}

void Elaborator::ValidateChandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (IsChandleVar(item->assign_lhs, var_types_) ||
      IsChandleVar(item->assign_rhs, var_types_)) {
    diag_.Error(item->loc, "chandle cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateChandleSensitivity(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (IsChandleVar(ev.signal, var_types_)) {
      diag_.Error(item->loc, "chandle cannot appear in event expression");
    }
  }
}

static bool IsNullLiteral(const Expr* e) {
  return e && e->kind == ExprKind::kIdentifier && e->text == "null";
}

static bool IsAllowedChandleBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static void CheckChandleExpr(const Expr* e, const TypeMap& types,
                             DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ch = e->lhs && IsChandleVar(e->lhs, types);
    bool rhs_ch = e->rhs && IsChandleVar(e->rhs, types);
    if ((lhs_ch || rhs_ch) && !IsAllowedChandleBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on chandle");
    }
  }
  if (e->kind == ExprKind::kUnary && IsChandleVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on chandle");
  }
  if (e->kind == ExprKind::kPostfixUnary && IsChandleVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on chandle");
  }
  if (e->kind == ExprKind::kSelect && e->base && IsChandleVar(e->base, types)) {
    diag.Error(e->range.start, "bit-select on chandle is illegal");
  }
  CheckChandleExpr(e->lhs, types, diag);
  CheckChandleExpr(e->rhs, types, diag);
  CheckChandleExpr(e->base, types, diag);
  CheckChandleExpr(e->index, types, diag);
  CheckChandleExpr(e->condition, types, diag);
  CheckChandleExpr(e->true_expr, types, diag);
  CheckChandleExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckChandleExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForChandleOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    bool lhs_ch = IsChandleVar(s->lhs, var_types_);
    bool rhs_ch = IsChandleVar(s->rhs, var_types_);
    if (lhs_ch && !rhs_ch && !IsNullLiteral(s->rhs)) {
      diag_.Error(s->range.start,
                  "chandle can only be assigned from another chandle or null");
    }
    if (!lhs_ch && rhs_ch) {
      diag_.Error(s->range.start,
                  "chandle cannot be assigned to a non-chandle variable");
    }
  }
  CheckChandleExpr(s->rhs, var_types_, diag_);
  CheckChandleExpr(s->expr, var_types_, diag_);
  CheckChandleExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForChandleOps(sub);
  WalkStmtsForChandleOps(s->then_branch);
  WalkStmtsForChandleOps(s->else_branch);
  WalkStmtsForChandleOps(s->body);
  WalkStmtsForChandleOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForChandleOps(ci.body);
}

void Elaborator::ValidateChandleOps(const ModuleDecl* decl) {
  bool has_chandle = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kChandle) {
      has_chandle = true;
      break;
    }
  }
  if (!has_chandle) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForChandleOps(item->body);
    }
  }
}

static bool IsVirtualInterfaceVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kVirtualInterface;
}

// §25.9: leftmost identifier of a (possibly hierarchical) reference, e.g. "u"
// for the defparam path u.W.
static std::string_view ReferenceRootName(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->lhs != nullptr) {
      e = e->lhs;
    } else if (e->base != nullptr) {
      e = e->base;
    } else {
      break;
    }
  }
  return {};
}

static bool ExprUsesVirtualInterface(const Expr* e, const TypeMap& types) {
  if (!e) return false;
  if (IsVirtualInterfaceVar(e, types)) return true;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      IsVirtualInterfaceVar(e->lhs, types)) {
    return true;
  }
  if (ExprUsesVirtualInterface(e->lhs, types)) return true;
  if (ExprUsesVirtualInterface(e->rhs, types)) return true;
  if (ExprUsesVirtualInterface(e->base, types)) return true;
  if (ExprUsesVirtualInterface(e->index, types)) return true;
  if (ExprUsesVirtualInterface(e->condition, types)) return true;
  if (ExprUsesVirtualInterface(e->true_expr, types)) return true;
  if (ExprUsesVirtualInterface(e->false_expr, types)) return true;
  for (const auto* elem : e->elements) {
    if (ExprUsesVirtualInterface(elem, types)) return true;
  }
  return false;
}

void Elaborator::ValidateVirtualInterfaceContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (ExprUsesVirtualInterface(item->assign_lhs, var_types_) ||
      ExprUsesVirtualInterface(item->assign_rhs, var_types_)) {
    diag_.Error(item->loc,
                "virtual interface cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateVirtualInterfaceSensitivity(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ExprUsesVirtualInterface(ev.signal, var_types_)) {
      diag_.Error(item->loc,
                  "virtual interface cannot appear in event expression");
    }
  }
}

static bool IsAllowedVirtualInterfaceBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

static void CheckVirtualInterfaceExpr(const Expr* e, const TypeMap& types,
                                      DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_vi = e->lhs && IsVirtualInterfaceVar(e->lhs, types);
    bool rhs_vi = e->rhs && IsVirtualInterfaceVar(e->rhs, types);
    if ((lhs_vi || rhs_vi) && !IsAllowedVirtualInterfaceBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on virtual interface");
    }
  }
  if (e->kind == ExprKind::kUnary && IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on virtual interface");
  }
  if (e->kind == ExprKind::kPostfixUnary &&
      IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on virtual interface");
  }
  if (e->kind == ExprKind::kSelect && e->base &&
      IsVirtualInterfaceVar(e->base, types)) {
    diag.Error(e->range.start, "bit-select on virtual interface is illegal");
  }
  CheckVirtualInterfaceExpr(e->lhs, types, diag);
  CheckVirtualInterfaceExpr(e->rhs, types, diag);
  CheckVirtualInterfaceExpr(e->base, types, diag);
  CheckVirtualInterfaceExpr(e->index, types, diag);
  CheckVirtualInterfaceExpr(e->condition, types, diag);
  CheckVirtualInterfaceExpr(e->true_expr, types, diag);
  CheckVirtualInterfaceExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckVirtualInterfaceExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForVirtualInterfaceOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    bool lhs_vi = IsVirtualInterfaceVar(s->lhs, var_types_);
    bool rhs_vi = IsVirtualInterfaceVar(s->rhs, var_types_);
    auto rhs_name = ExprIdent(s->rhs);
    bool rhs_is_iface_inst =
        !rhs_name.empty() && interface_inst_types_.count(rhs_name) != 0;
    if (lhs_vi && !rhs_vi && !rhs_is_iface_inst && !IsNullLiteral(s->rhs)) {
      diag_.Error(s->range.start,
                  "virtual interface can only be assigned from another "
                  "virtual interface, an interface instance, or null");
    }
    if (lhs_vi && rhs_vi) {
      auto lhs_name = ExprIdent(s->lhs);
      auto lit = vi_var_interface_types_.find(lhs_name);
      auto rit = vi_var_interface_types_.find(rhs_name);
      if (lit != vi_var_interface_types_.end() &&
          rit != vi_var_interface_types_.end() && lit->second != rit->second) {
        diag_.Error(s->range.start,
                    "virtual interface assignment between incompatible "
                    "interface types");
      }
      auto lmp = vi_var_modports_.find(lhs_name);
      auto rmp = vi_var_modports_.find(rhs_name);
      bool lhs_has_mp = lmp != vi_var_modports_.end() && !lmp->second.empty();
      bool rhs_has_mp = rmp != vi_var_modports_.end() && !rmp->second.empty();
      if (!lhs_has_mp && rhs_has_mp) {
        diag_.Error(s->range.start,
                    "virtual interface with modport cannot be assigned to "
                    "virtual interface without modport");
      } else if (lhs_has_mp && rhs_has_mp && lmp->second != rmp->second) {
        diag_.Error(s->range.start, "virtual interface modports do not match");
      }
      // §25.9: the actual parameter values shall match for two virtual
      // interfaces to be of the same type and assignment compatible.
      auto lpv = vi_var_param_values_.find(lhs_name);
      auto rpv = vi_var_param_values_.find(rhs_name);
      if (lpv != vi_var_param_values_.end() &&
          rpv != vi_var_param_values_.end() && lpv->second != rpv->second) {
        diag_.Error(s->range.start,
                    "virtual interface parameter values do not match");
      }
    }
    if (lhs_vi && rhs_is_iface_inst) {
      auto lhs_name = ExprIdent(s->lhs);
      auto lit = vi_var_interface_types_.find(lhs_name);
      auto iit = interface_inst_types_.find(rhs_name);
      if (lit != vi_var_interface_types_.end() &&
          iit != interface_inst_types_.end() && lit->second != iit->second) {
        diag_.Error(s->range.start,
                    "virtual interface assignment from interface instance of "
                    "incompatible type");
      }
      // §25.9: the actual parameter values of the interface instance shall
      // match those of the virtual interface.
      auto lpv = vi_var_param_values_.find(lhs_name);
      auto ipv = interface_inst_param_values_.find(rhs_name);
      if (lpv != vi_var_param_values_.end() &&
          ipv != interface_inst_param_values_.end() &&
          lpv->second != ipv->second) {
        diag_.Error(s->range.start,
                    "virtual interface parameter values do not match the "
                    "interface instance");
      }
      // §25.9: it is illegal to assign an interface instance to a virtual
      // interface when a defparam targeting that instance is declared outside
      // the interface.
      if (vi_external_defparam_insts_.count(rhs_name)) {
        diag_.Error(s->range.start,
                    "interface instance targeted by a defparam declared "
                    "outside the interface cannot be assigned to a virtual "
                    "interface");
      }
    }
    if (!lhs_vi && rhs_vi) {
      diag_.Error(s->range.start,
                  "virtual interface cannot be assigned to a non-virtual-"
                  "interface variable");
    }
  }
  CheckVirtualInterfaceExpr(s->rhs, var_types_, diag_);
  CheckVirtualInterfaceExpr(s->expr, var_types_, diag_);
  CheckVirtualInterfaceExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForVirtualInterfaceOps(sub);
  WalkStmtsForVirtualInterfaceOps(s->then_branch);
  WalkStmtsForVirtualInterfaceOps(s->else_branch);
  WalkStmtsForVirtualInterfaceOps(s->body);
  WalkStmtsForVirtualInterfaceOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForVirtualInterfaceOps(ci.body);
}

void Elaborator::ValidateVirtualInterfaceOps(const ModuleDecl* decl) {
  bool has_vi = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kVirtualInterface) {
      has_vi = true;
      break;
    }
  }
  if (!has_vi) return;
  // §25.9: a defparam declared in this scope (i.e. outside the interface)
  // targeting an interface instance taints that instance for assignment to a
  // virtual interface.
  vi_external_defparam_insts_.clear();
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& assign : item->defparam_assigns) {
      auto root = ReferenceRootName(assign.first);
      if (!root.empty() && interface_inst_types_.count(root)) {
        vi_external_defparam_insts_.insert(root);
      }
    }
  }
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForVirtualInterfaceOps(item->body);
    }
  }
}

static bool IsEventVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kEvent;
}

// §15.5.5.3: an event variable may be compared against another event or null
// only with equality (==), inequality (!=), case equality (===), or case
// inequality (!==). The four case/logical equality operators are the only
// binary operators allowed on an event operand.
static bool IsAllowedEventBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

// §15.5.5.3: reject any operator applied to an event variable other than the
// permitted comparisons (and the implicit Boolean test, which uses the event
// directly rather than through an operator node). Arithmetic, relational,
// bitwise, unary, and select operators on events are all illegal.
static void CheckEventExpr(const Expr* e, const TypeMap& types,
                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ev = e->lhs && IsEventVar(e->lhs, types);
    bool rhs_ev = e->rhs && IsEventVar(e->rhs, types);
    if ((lhs_ev || rhs_ev) && !IsAllowedEventBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on event variable");
    }
  }
  if (e->kind == ExprKind::kUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on event variable");
  }
  if (e->kind == ExprKind::kPostfixUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on event variable");
  }
  CheckEventExpr(e->lhs, types, diag);
  CheckEventExpr(e->rhs, types, diag);
  CheckEventExpr(e->base, types, diag);
  CheckEventExpr(e->index, types, diag);
  CheckEventExpr(e->condition, types, diag);
  CheckEventExpr(e->true_expr, types, diag);
  CheckEventExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckEventExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForEventOps(const Stmt* s) {
  if (!s) return;
  // Event-control event lists (s->events) are not operator expressions and are
  // intentionally left untouched here; only value expressions are inspected.
  CheckEventExpr(s->rhs, var_types_, diag_);
  CheckEventExpr(s->expr, var_types_, diag_);
  CheckEventExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForEventOps(sub);
  WalkStmtsForEventOps(s->then_branch);
  WalkStmtsForEventOps(s->else_branch);
  WalkStmtsForEventOps(s->body);
  WalkStmtsForEventOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForEventOps(ci.body);
}

void Elaborator::ValidateEventOps(const ModuleDecl* decl) {
  bool has_event = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kEvent) {
      has_event = true;
      break;
    }
  }
  if (!has_event) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForEventOps(item->body);
    }
  }
}

}  // namespace delta
