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
    // §10.10: a concatenation assigned to a chandle array or queue is an
    // unpacked array concatenation, not a scalar chandle assignment; its
    // per-element null legality is checked in CheckNullItemInArrayConcatAssign,
    // so the scalar "= another chandle or null" rule does not apply here.
    bool unpacked_concat_target =
        s->lhs->kind == ExprKind::kIdentifier &&
        var_array_info_.count(s->lhs->text) > 0 &&
        (s->rhs->kind == ExprKind::kConcatenation ||
         s->rhs->kind == ExprKind::kAssignmentPattern);
    if (lhs_ch && !rhs_ch && !IsNullLiteral(s->rhs) &&
        !unpacked_concat_target) {
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

// §25.9: == / != between two virtual interfaces is legal only when they have
// the same interface type. Reports when both operands are vif variables whose
// recorded interface types differ.
static void CheckViEqualitySameType(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, std::string_view>& vi_iface,
    DiagEngine& diag) {
  if (e->kind != ExprKind::kBinary || !e->lhs || !e->rhs) return;
  if (!IsAllowedVirtualInterfaceBinaryOp(e->op)) return;
  if (!IsVirtualInterfaceVar(e->lhs, types) ||
      !IsVirtualInterfaceVar(e->rhs, types))
    return;
  auto lit = vi_iface.find(ExprIdent(e->lhs));
  auto rit = vi_iface.find(ExprIdent(e->rhs));
  if (lit != vi_iface.end() && rit != vi_iface.end() &&
      lit->second != rit->second) {
    diag.Error(e->range.start,
               "comparison between virtual interfaces of different types");
  }
}

static void CheckVirtualInterfaceExpr(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, std::string_view>& vi_iface,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_vi = e->lhs && IsVirtualInterfaceVar(e->lhs, types);
    bool rhs_vi = e->rhs && IsVirtualInterfaceVar(e->rhs, types);
    if ((lhs_vi || rhs_vi) && !IsAllowedVirtualInterfaceBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on virtual interface");
    }
    CheckViEqualitySameType(e, types, vi_iface, diag);
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
  CheckVirtualInterfaceExpr(e->lhs, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->rhs, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->base, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->index, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->condition, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->true_expr, types, vi_iface, diag);
  CheckVirtualInterfaceExpr(e->false_expr, types, vi_iface, diag);
  for (const auto* elem : e->elements) {
    CheckVirtualInterfaceExpr(elem, types, vi_iface, diag);
  }
}

using ViStringMap = std::unordered_map<std::string_view, std::string_view>;
using ViParamMap = std::unordered_map<std::string_view, std::vector<int64_t>>;

// §25.9: two virtual interfaces are of the same type only when their interface
// types match.
static void CheckViToViInterfaceTypes(std::string_view lhs_name,
                                      std::string_view rhs_name,
                                      const ViStringMap& vi_var_interface_types,
                                      SourceLoc loc, DiagEngine& diag) {
  auto lit = vi_var_interface_types.find(lhs_name);
  auto rit = vi_var_interface_types.find(rhs_name);
  if (lit != vi_var_interface_types.end() &&
      rit != vi_var_interface_types.end() && lit->second != rit->second) {
    diag.Error(loc,
               "virtual interface assignment between incompatible "
               "interface types");
  }
}

// §25.9: modports must match for two virtual interfaces to be assignment
// compatible.
static void CheckViToViModports(std::string_view lhs_name,
                                std::string_view rhs_name,
                                const ViStringMap& vi_var_modports,
                                SourceLoc loc, DiagEngine& diag) {
  auto lmp = vi_var_modports.find(lhs_name);
  auto rmp = vi_var_modports.find(rhs_name);
  bool lhs_has_mp = lmp != vi_var_modports.end() && !lmp->second.empty();
  bool rhs_has_mp = rmp != vi_var_modports.end() && !rmp->second.empty();
  if (!lhs_has_mp && rhs_has_mp) {
    diag.Error(loc,
               "virtual interface with modport cannot be assigned to "
               "virtual interface without modport");
  } else if (lhs_has_mp && rhs_has_mp && lmp->second != rmp->second) {
    diag.Error(loc, "virtual interface modports do not match");
  }
}

// §25.9: the actual parameter values shall match for two virtual interfaces to
// be of the same type and assignment compatible.
static void CheckViToViParamValues(std::string_view lhs_name,
                                   std::string_view rhs_name,
                                   const ViParamMap& vi_var_param_values,
                                   SourceLoc loc, DiagEngine& diag) {
  auto lpv = vi_var_param_values.find(lhs_name);
  auto rpv = vi_var_param_values.find(rhs_name);
  if (lpv != vi_var_param_values.end() && rpv != vi_var_param_values.end() &&
      lpv->second != rpv->second) {
    diag.Error(loc, "virtual interface parameter values do not match");
  }
}

// Parameter bundle for virtual-interface assignment checking, grouping the
// elaborator state needed to validate a single assignment statement (§25.9) so
// it can be threaded through the free helpers without member access. It holds
// the per-name descriptors of both assignment entities: the virtual-interface
// variable (vi_var_*) and the interface instance (interface_inst_*).
struct ViAssignContext {
  const TypeMap& var_types;
  const ViStringMap& interface_inst_types;
  const ViStringMap& vi_var_interface_types;
  const ViStringMap& vi_var_modports;
  const ViParamMap& vi_var_param_values;
  const ViParamMap& interface_inst_param_values;
  const std::unordered_set<std::string_view>& vi_external_defparam_insts;
};

// §25.9: two virtual interfaces are of the same type, and hence assignment
// compatible, only when their interface types, modports, and actual parameter
// values all match.
static void CheckViToViAssign(std::string_view lhs_name,
                              std::string_view rhs_name,
                              const ViAssignContext& ctx, SourceLoc loc,
                              DiagEngine& diag) {
  CheckViToViInterfaceTypes(lhs_name, rhs_name, ctx.vi_var_interface_types, loc,
                            diag);
  CheckViToViModports(lhs_name, rhs_name, ctx.vi_var_modports, loc, diag);
  CheckViToViParamValues(lhs_name, rhs_name, ctx.vi_var_param_values, loc,
                         diag);
}

// §25.9: assigning an interface instance to a virtual interface requires a
// matching interface type.
static void CheckViFromInstanceTypes(std::string_view lhs_name,
                                     std::string_view rhs_name,
                                     const ViAssignContext& ctx, SourceLoc loc,
                                     DiagEngine& diag) {
  auto lit = ctx.vi_var_interface_types.find(lhs_name);
  auto iit = ctx.interface_inst_types.find(rhs_name);
  if (lit != ctx.vi_var_interface_types.end() &&
      iit != ctx.interface_inst_types.end() && lit->second != iit->second) {
    diag.Error(loc,
               "virtual interface assignment from interface instance of "
               "incompatible type");
  }
}

// §25.9: the actual parameter values of the interface instance shall match
// those of the virtual interface.
static void CheckViFromInstanceParamValues(std::string_view lhs_name,
                                           std::string_view rhs_name,
                                           const ViAssignContext& ctx,
                                           SourceLoc loc, DiagEngine& diag) {
  auto lpv = ctx.vi_var_param_values.find(lhs_name);
  auto ipv = ctx.interface_inst_param_values.find(rhs_name);
  if (lpv != ctx.vi_var_param_values.end() &&
      ipv != ctx.interface_inst_param_values.end() &&
      lpv->second != ipv->second) {
    diag.Error(loc,
               "virtual interface parameter values do not match the "
               "interface instance");
  }
}

// §25.9: it is illegal to assign an interface instance to a virtual interface
// when a defparam targeting that instance is declared outside the interface.
static void CheckViFromInstanceDefparam(
    std::string_view rhs_name,
    const std::unordered_set<std::string_view>& vi_external_defparam_insts,
    SourceLoc loc, DiagEngine& diag) {
  if (vi_external_defparam_insts.count(rhs_name)) {
    diag.Error(loc,
               "interface instance targeted by a defparam declared "
               "outside the interface cannot be assigned to a virtual "
               "interface");
  }
}

// §25.9: assigning an interface instance to a virtual interface requires
// matching interface type and actual parameter values, and is forbidden when a
// defparam declared outside the interface targets that instance.
static void CheckViFromInstanceAssign(std::string_view lhs_name,
                                      std::string_view rhs_name,
                                      const ViAssignContext& ctx, SourceLoc loc,
                                      DiagEngine& diag) {
  CheckViFromInstanceTypes(lhs_name, rhs_name, ctx, loc, diag);
  CheckViFromInstanceParamValues(lhs_name, rhs_name, ctx, loc, diag);
  CheckViFromInstanceDefparam(rhs_name, ctx.vi_external_defparam_insts, loc,
                              diag);
}

// §25.9: validate a single blocking/nonblocking assignment whose operands may
// involve virtual interfaces, interface instances, or null.
static void CheckVirtualInterfaceAssignStmt(const Stmt* s,
                                            const ViAssignContext& ctx,
                                            DiagEngine& diag) {
  bool lhs_vi = IsVirtualInterfaceVar(s->lhs, ctx.var_types);
  bool rhs_vi = IsVirtualInterfaceVar(s->rhs, ctx.var_types);
  auto rhs_name = ExprIdent(s->rhs);
  bool rhs_is_iface_inst =
      !rhs_name.empty() && ctx.interface_inst_types.count(rhs_name) != 0;
  if (lhs_vi && !rhs_vi && !rhs_is_iface_inst && !IsNullLiteral(s->rhs)) {
    diag.Error(s->range.start,
               "virtual interface can only be assigned from another "
               "virtual interface, an interface instance, or null");
  }
  if (lhs_vi && rhs_vi) {
    CheckViToViAssign(ExprIdent(s->lhs), rhs_name, ctx, s->range.start, diag);
  }
  if (lhs_vi && rhs_is_iface_inst) {
    CheckViFromInstanceAssign(ExprIdent(s->lhs), rhs_name, ctx, s->range.start,
                              diag);
  }
  if (!lhs_vi && rhs_vi) {
    diag.Error(s->range.start,
               "virtual interface cannot be assigned to a non-virtual-"
               "interface variable");
  }
}

void Elaborator::WalkStmtsForVirtualInterfaceOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    const ViAssignContext kCtx{var_types_,
                               interface_inst_types_,
                               vi_var_interface_types_,
                               vi_var_modports_,
                               vi_var_param_values_,
                               interface_inst_param_values_,
                               vi_external_defparam_insts_};
    CheckVirtualInterfaceAssignStmt(s, kCtx, diag_);
  }
  CheckVirtualInterfaceExpr(s->rhs, var_types_, vi_var_interface_types_, diag_);
  CheckVirtualInterfaceExpr(s->expr, var_types_, vi_var_interface_types_,
                            diag_);
  CheckVirtualInterfaceExpr(s->condition, var_types_, vi_var_interface_types_,
                            diag_);
  for (auto* sub : s->stmts) WalkStmtsForVirtualInterfaceOps(sub);
  WalkStmtsForVirtualInterfaceOps(s->then_branch);
  WalkStmtsForVirtualInterfaceOps(s->else_branch);
  WalkStmtsForVirtualInterfaceOps(s->body);
  WalkStmtsForVirtualInterfaceOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForVirtualInterfaceOps(ci.body);
}

static bool ScopeHasVirtualInterfaceVar(const TypeMap& types) {
  for (const auto& [name, kind] : types) {
    if (kind == DataTypeKind::kVirtualInterface) return true;
  }
  return false;
}

// §25.9: a defparam declared in this scope (i.e. outside the interface)
// targeting an interface instance taints that instance for assignment to a
// virtual interface.
static void CollectExternalDefparamInsts(
    const ModuleDecl* decl, const ViStringMap& interface_inst_types,
    std::unordered_set<std::string_view>& vi_external_defparam_insts) {
  vi_external_defparam_insts.clear();
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& assign : item->defparam_assigns) {
      auto root = ReferenceRootName(assign.first);
      if (!root.empty() && interface_inst_types.count(root)) {
        vi_external_defparam_insts.insert(root);
      }
    }
  }
}

void Elaborator::ValidateVirtualInterfaceOps(const ModuleDecl* decl) {
  if (!ScopeHasVirtualInterfaceVar(var_types_)) return;
  CollectExternalDefparamInsts(decl, interface_inst_types_,
                               vi_external_defparam_insts_);
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
