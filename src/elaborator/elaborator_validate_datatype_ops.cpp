#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "elaborator/virtual_interface_modports.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

template <typename IsReal>
static bool HasEdgeOnReal(const std::vector<EventExpr>& events,
                          IsReal&& is_real) {
  for (const auto& ev : events) {
    if (ev.edge == Edge::kNone) continue;
    auto name = ExprIdent(ev.signal);
    if (!name.empty() && is_real(name)) return true;
  }
  return false;
}

template <typename IsModuleReal>
static void ReportEdgeOnRealInStmt(const Stmt* s,
                                   std::vector<std::string_view>& locals,
                                   IsModuleReal&& is_module_real,
                                   DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (IsRealType(s->var_decl_type.kind) && s->var_unpacked_dims.empty())
      locals.push_back(s->var_name);
    return;
  }
  auto is_real = [&](std::string_view name) {
    return std::find(locals.begin(), locals.end(), name) != locals.end() ||
           is_module_real(name);
  };
  if (HasEdgeOnReal(s->events, is_real)) {
    diag.Error(s->range.start, "edge event on real type is illegal",
               Subclause("6.12"));
  }
  const size_t kOuter = locals.size();
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    ReportEdgeOnRealInStmt(sub, locals, is_module_real, diag);
  });
  locals.resize(kOuter);
}

void Elaborator::ValidateEdgeOnReal(const ModuleItem* item) {
  auto is_module_real = [this](std::string_view name) {
    auto it = var_types_.find(name);
    return it != var_types_.end() && IsRealType(it->second);
  };
  if (IsProceduralItemKind(item->kind) &&
      HasEdgeOnReal(item->sensitivity, is_module_real)) {
    diag_.Error(item->loc, "edge event on real type is illegal",
                Subclause("6.12"));
  }
  std::vector<std::string_view> locals;
  ReportEdgeOnRealInStmt(item->body, locals, is_module_real, diag_);
  for (const auto* s : item->func_body_stmts)
    ReportEdgeOnRealInStmt(s, locals, is_module_real, diag_);
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
    diag_.Error(item->loc, "chandle cannot be used in continuous assignment",
                Subclause("6.14"));
  }
}

void Elaborator::ValidateChandleSensitivity(const ModuleItem* item) {
  if (!IsProceduralItemKind(item->kind)) return;
  for (const auto& ev : item->sensitivity) {
    if (IsChandleVar(ev.signal, var_types_)) {
      diag_.Error(item->loc, "chandle cannot appear in event expression",
                  Subclause("6.14"));
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

static void CheckChandleOperandUse(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        arrays,
    DiagEngine& diag) {
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ch = e->lhs && IsChandleVar(e->lhs, types);
    bool rhs_ch = e->rhs && IsChandleVar(e->rhs, types);
    if ((lhs_ch || rhs_ch) && !IsAllowedChandleBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on chandle",
                 Subclause("6.14"));
    }
    return;
  }
  if ((e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
      IsChandleVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on chandle",
               Subclause("6.14"));
    return;
  }
  if (e->kind == ExprKind::kSelect && e->base && IsChandleVar(e->base, types) &&
      arrays.find(ExprIdent(e->base)) == arrays.end()) {
    diag.Error(e->range.start, "bit-select on chandle is illegal",
               Subclause("6.14"));
  }
}

static void CheckChandleExpr(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        arrays,
    DiagEngine& diag) {
  if (!e) return;
  CheckChandleOperandUse(e, types, arrays, diag);
  CheckChandleExpr(e->lhs, types, arrays, diag);
  CheckChandleExpr(e->rhs, types, arrays, diag);
  CheckChandleExpr(e->base, types, arrays, diag);
  CheckChandleExpr(e->index, types, arrays, diag);
  CheckChandleExpr(e->condition, types, arrays, diag);
  CheckChandleExpr(e->true_expr, types, arrays, diag);
  CheckChandleExpr(e->false_expr, types, arrays, diag);
  for (const auto* elem : e->elements) {
    CheckChandleExpr(elem, types, arrays, diag);
  }
}

static bool YieldsChandle(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        arrays) {
  if (IsChandleVar(e, types)) return true;
  if (!e || e->kind != ExprKind::kSelect) return false;
  return IsChandleVar(e->base, types) &&
         arrays.find(ExprIdent(e->base)) != arrays.end();
}

static bool CallYieldsChandle(
    const Expr* e, const std::unordered_set<std::string_view>& chandle_funcs) {
  return e != nullptr && e->kind == ExprKind::kCall &&
         chandle_funcs.count(e->callee) != 0;
}

void Elaborator::WalkStmtsForChandleOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    bool lhs_ch = YieldsChandle(s->lhs, var_types_, var_array_info_);
    bool rhs_ch = YieldsChandle(s->rhs, var_types_, var_array_info_) ||
                  CallYieldsChandle(s->rhs, chandle_result_funcs_);
    bool unpacked_concat_target =
        s->lhs->kind == ExprKind::kIdentifier &&
        var_array_info_.count(s->lhs->text) > 0 &&
        (s->rhs->kind == ExprKind::kConcatenation ||
         s->rhs->kind == ExprKind::kAssignmentPattern);
    if (lhs_ch && !rhs_ch && !IsNullLiteral(s->rhs) &&
        !unpacked_concat_target) {
      diag_.Error(s->range.start,
                  "chandle can only be assigned from another chandle or null",
                  Subclause("6.14"));
    }
    if (!lhs_ch && rhs_ch) {
      diag_.Error(s->range.start,
                  "chandle cannot be assigned to a non-chandle variable",
                  Subclause("6.14"));
    }
  }
  CheckChandleExpr(s->rhs, var_types_, var_array_info_, diag_);
  CheckChandleExpr(s->expr, var_types_, var_array_info_, diag_);
  CheckChandleExpr(s->condition, var_types_, var_array_info_, diag_);
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForChandleOps(sub); });
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
  chandle_result_funcs_.clear();
  for (const auto* item : decl->items) {
    bool is_func = item->kind == ModuleItemKind::kFunctionDecl ||
                   item->kind == ModuleItemKind::kDpiImport;
    if (is_func && item->return_type.kind == DataTypeKind::kChandle) {
      chandle_result_funcs_.insert(item->name);
    }
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
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
  const Expr* const kChildren[] = {
      e->lhs,          e->rhs,       e->base,        e->index,
      e->index_end,    e->condition, e->true_expr,   e->false_expr,
      e->repeat_count, e->with_expr, e->stream_range};
  for (const auto* child : kChildren) {
    if (ExprUsesVirtualInterface(child, types)) return true;
  }
  for (const auto* arg : e->args) {
    if (ExprUsesVirtualInterface(arg, types)) return true;
  }
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
                "virtual interface cannot be used in continuous assignment",
                Subclause("25.9"));
  }
}

static bool InfersItsSensitivityList(const ModuleItem* item) {
  if (item->kind == ModuleItemKind::kAlwaysCombBlock) return true;
  if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return true;
  return item->kind == ModuleItemKind::kAlwaysBlock &&
         item->is_star_sensitivity;
}

void Elaborator::ReportVirtualInterfaceInInferredSensitivity(
    const ModuleItem* item) {
  if (!InfersItsSensitivityList(item)) return;
  bool reported = false;
  ForEachStmtReadExpr(item->body, [&](const Expr* e) {
    if (reported || !ExprUsesVirtualInterface(e, var_types_)) return;
    diag_.Error(item->loc,
                "virtual interface cannot appear in an inferred sensitivity "
                "list",
                Subclause("25.9"));
    reported = true;
  });
}

void Elaborator::ValidateVirtualInterfaceSensitivity(const ModuleItem* item) {
  if (!IsProceduralItemKind(item->kind)) return;
  ReportVirtualInterfaceInInferredSensitivity(item);
  for (const auto& ev : item->sensitivity) {
    if (ExprUsesVirtualInterface(ev.signal, var_types_) ||
        ExprUsesVirtualInterface(ev.iff_condition, var_types_)) {
      diag_.Error(item->loc,
                  "virtual interface cannot appear in event expression",
                  Subclause("25.9"));
    }
  }
}

static bool IsAllowedVirtualInterfaceBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

static bool IsLiteralExpr(const Expr* e) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    default:
      return false;
  }
}

static bool IsNonVirtualInterfaceVar(const Expr* e, const TypeMap& types) {
  if (e->kind != ExprKind::kIdentifier) return false;
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second != DataTypeKind::kVirtualInterface;
}

static void CheckViPairSameInterface(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& vi_iface,
    DiagEngine& diag) {
  auto lit = vi_iface.find(ExprIdent(e->lhs));
  auto rit = vi_iface.find(ExprIdent(e->rhs));
  if (lit != vi_iface.end() && rit != vi_iface.end() &&
      lit->second != rit->second) {
    diag.Error(e->range.start,
               "comparison between virtual interfaces of different types",
               Subclause("25.9"));
  }
}

static void CheckViAgainstInstance(
    const Expr* e, const Expr* vi_side, std::string_view inst_iface,
    const std::unordered_map<std::string_view, std::string_view>& vi_iface,
    DiagEngine& diag) {
  auto vit = vi_iface.find(ExprIdent(vi_side));
  if (vit != vi_iface.end() && vit->second != inst_iface) {
    diag.Error(e->range.start,
               "comparison between a virtual interface and an interface "
               "instance of a different type",
               Subclause("25.9"));
  }
}

static void CheckViEqualityOperands(
    const Expr* e, const TypeMap& types,
    const std::unordered_map<std::string_view, std::string_view>& vi_iface,
    const std::unordered_map<std::string_view, std::string_view>&
        interface_inst,
    DiagEngine& diag) {
  if (e->kind != ExprKind::kBinary || !e->lhs || !e->rhs) return;
  if (!IsAllowedVirtualInterfaceBinaryOp(e->op)) return;
  bool lhs_vi = IsVirtualInterfaceVar(e->lhs, types);
  bool rhs_vi = IsVirtualInterfaceVar(e->rhs, types);
  if (!lhs_vi && !rhs_vi) return;
  if (lhs_vi && rhs_vi) {
    CheckViPairSameInterface(e, vi_iface, diag);
    return;
  }
  const Expr* other = lhs_vi ? e->rhs : e->lhs;
  const Expr* vi_side = lhs_vi ? e->lhs : e->rhs;
  if (IsNullLiteral(other)) return;
  auto other_name = ExprIdent(other);
  auto inst_it = other_name.empty() ? interface_inst.end()
                                    : interface_inst.find(other_name);
  if (inst_it != interface_inst.end()) {
    CheckViAgainstInstance(e, vi_side, inst_it->second, vi_iface, diag);
    return;
  }
  if (IsLiteralExpr(other) || IsNonVirtualInterfaceVar(other, types)) {
    diag.Error(e->range.start,
               "virtual interface can only be compared with another virtual "
               "interface, an interface instance, or null",
               Subclause("25.9"));
  }
}

struct ViExprTables {
  const TypeMap& types;
  const std::unordered_map<std::string_view, std::string_view>& vi_iface;
  const std::unordered_map<std::string_view, std::string_view>& interface_inst;
  const std::unordered_map<std::string_view, std::size_t>& array_dims;
};

static bool SelectsIntoVifElement(
    const Expr* e,
    const std::unordered_map<std::string_view, std::size_t>& array_dims) {
  std::size_t selects = 0;
  while (e->kind == ExprKind::kSelect) {
    ++selects;
    e = e->base;
  }
  if (e->kind != ExprKind::kIdentifier) return false;
  const auto kDims = array_dims.find(e->text);
  return kDims != array_dims.end() && selects > kDims->second;
}

static void ReportViOperation(const Expr* e, const ViExprTables& tables,
                              DiagEngine& diag) {
  const TypeMap& types = tables.types;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_vi = e->lhs && IsVirtualInterfaceVar(e->lhs, types);
    bool rhs_vi = e->rhs && IsVirtualInterfaceVar(e->rhs, types);
    if ((lhs_vi || rhs_vi) && !IsAllowedVirtualInterfaceBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on virtual interface",
                 Subclause("25.9"));
    }
    CheckViEqualityOperands(e, types, tables.vi_iface, tables.interface_inst,
                            diag);
  }
  if (e->kind == ExprKind::kUnary && IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on virtual interface",
               Subclause("25.9"));
  }
  if (e->kind == ExprKind::kPostfixUnary &&
      IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on virtual interface",
               Subclause("25.9"));
  }
  if (e->kind == ExprKind::kSelect && e->base &&
      (IsVirtualInterfaceVar(e->base, types) ||
       SelectsIntoVifElement(e, tables.array_dims))) {
    diag.Error(e->range.start, "bit-select on virtual interface is illegal",
               Subclause("25.9"));
  }
}

static void CheckVirtualInterfaceExpr(const Expr* e, const ViExprTables& tables,
                                      DiagEngine& diag) {
  if (!e) return;
  ReportViOperation(e, tables, diag);
  const Expr* const kChildren[] = {e->lhs,       e->rhs,       e->base,
                                   e->index,     e->condition, e->true_expr,
                                   e->false_expr};
  for (const Expr* child : kChildren) {
    CheckVirtualInterfaceExpr(child, tables, diag);
  }
  for (const auto* elem : e->elements) {
    CheckVirtualInterfaceExpr(elem, tables, diag);
  }
}

using ViStringMap = std::unordered_map<std::string_view, std::string_view>;
using ViParamMap = std::unordered_map<std::string_view, std::vector<int64_t>>;

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
               "interface types",
               Subclause("25.9"));
  }
}

static void CheckViToViModports(std::string_view lhs_name,
                                std::string_view rhs_name,
                                const ViStringMap& vi_var_modports,
                                SourceLoc loc, DiagEngine& diag) {
  auto rmp = vi_var_modports.find(rhs_name);
  CheckViModportsMatch(
      lhs_name, rmp != vi_var_modports.end() ? rmp->second : std::string_view{},
      vi_var_modports, loc, diag);
}

static void CheckViToViParamValues(std::string_view lhs_name,
                                   std::string_view rhs_name,
                                   const ViParamMap& vi_var_param_values,
                                   SourceLoc loc, DiagEngine& diag) {
  auto lpv = vi_var_param_values.find(lhs_name);
  auto rpv = vi_var_param_values.find(rhs_name);
  if (lpv != vi_var_param_values.end() && rpv != vi_var_param_values.end() &&
      lpv->second != rpv->second) {
    diag.Error(loc, "virtual interface parameter values do not match",
               Subclause("25.9"));
  }
}

struct ViAssignContext {
  const TypeMap& var_types;
  const ViStringMap& interface_inst_types;
  const ViStringMap& vi_var_interface_types;
  const ViStringMap& vi_var_modports;
  const ViParamMap& vi_var_param_values;
  const ViParamMap& interface_inst_param_values;
  const std::unordered_set<std::string_view>& vi_external_defparam_insts;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
};

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
               "incompatible type",
               Subclause("25.9"));
  }
}

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
               "interface instance",
               Subclause("25.9"));
  }
}

static void CheckViFromInstanceDefparam(
    std::string_view rhs_name,
    const std::unordered_set<std::string_view>& vi_external_defparam_insts,
    SourceLoc loc, DiagEngine& diag) {
  if (vi_external_defparam_insts.count(rhs_name)) {
    diag.Error(loc,
               "interface instance targeted by a defparam declared "
               "outside the interface cannot be assigned to a virtual "
               "interface",
               Subclause("25.9"));
  }
}

static void CheckViFromInstanceAssign(std::string_view lhs_name,
                                      std::string_view rhs_name,
                                      const ViAssignContext& ctx, SourceLoc loc,
                                      DiagEngine& diag) {
  CheckViFromInstanceTypes(lhs_name, rhs_name, ctx, loc, diag);
  CheckViFromInstanceParamValues(lhs_name, rhs_name, ctx, loc, diag);
  CheckViFromInstanceDefparam(rhs_name, ctx.vi_external_defparam_insts, loc,
                              diag);
}

static void CheckVirtualInterfaceAssignStmt(const Stmt* s,
                                            const ViAssignContext& ctx,
                                            DiagEngine& diag) {
  bool lhs_vi = IsVirtualInterfaceVar(s->lhs, ctx.var_types);
  bool rhs_vi = IsVirtualInterfaceVar(s->rhs, ctx.var_types);
  auto rhs_name = ExprIdent(s->rhs);
  bool rhs_is_iface_inst =
      !rhs_name.empty() && ctx.interface_inst_types.count(rhs_name) != 0;
  bool rhs_plainly_not_vi = !IsNullLiteral(s->rhs) &&
                            (IsLiteralExpr(s->rhs) ||
                             IsNonVirtualInterfaceVar(s->rhs, ctx.var_types));
  if (lhs_vi && !rhs_vi && !rhs_is_iface_inst && rhs_plainly_not_vi) {
    diag.Error(s->range.start,
               "virtual interface can only be assigned from another "
               "virtual interface, an interface instance, or null",
               Subclause("25.9"));
  }
  if (lhs_vi && rhs_vi) {
    CheckViToViAssign(ExprIdent(s->lhs), rhs_name, ctx, s->range.start, diag);
  }
  if (lhs_vi && rhs_is_iface_inst) {
    CheckViFromInstanceAssign(ExprIdent(s->lhs), rhs_name, ctx, s->range.start,
                              diag);
  }
  if (lhs_vi && s->rhs->kind == ExprKind::kMemberAccess) {
    CheckViFromInstanceModport(
        s->lhs, s->rhs,
        {ctx.interface_inst_types, ctx.vi_var_modports, ctx.find_module},
        s->range.start, diag);
  }
  if (!lhs_vi && rhs_vi) {
    diag.Error(s->range.start,
               "virtual interface cannot be assigned to a non-virtual-"
               "interface variable",
               Subclause("25.9"));
  }
}

void Elaborator::WalkStmtsForVirtualInterfaceOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    const std::function<const ModuleDecl*(std::string_view)> kFindModule =
        [this](std::string_view name) { return FindModuleInScope(name); };
    const ViAssignContext kCtx{var_types_,
                               interface_inst_types_,
                               vi_var_interface_types_,
                               vi_var_modports_,
                               vi_var_param_values_,
                               interface_inst_param_values_,
                               vi_external_defparam_insts_,
                               kFindModule};
    CheckVirtualInterfaceAssignStmt(s, kCtx, diag_);
  }
  const ViExprTables kTables{vi_expr_types_, vi_var_interface_types_,
                             interface_inst_types_, vi_array_dims_};
  CheckVirtualInterfaceExpr(s->rhs, kTables, diag_);
  CheckVirtualInterfaceExpr(s->expr, kTables, diag_);
  CheckVirtualInterfaceExpr(s->condition, kTables, diag_);
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForVirtualInterfaceOps(sub); });
}

static bool ScopeHasVirtualInterfaceVar(const TypeMap& types) {
  for (const auto& [name, kind] : types) {
    if (kind == DataTypeKind::kVirtualInterface) return true;
  }
  return false;
}

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
  vi_expr_types_ = var_types_;
  vi_array_dims_.clear();
  for (const auto* item : decl->items) {
    if (item->unpacked_dims.empty()) continue;
    vi_expr_types_.erase(item->name);
    if (item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      vi_array_dims_[item->name] = item->unpacked_dims.size();
    }
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
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

static bool IsAllowedEventBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

static void CheckEventExpr(const Expr* e, const TypeMap& types,
                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ev = e->lhs && IsEventVar(e->lhs, types);
    bool rhs_ev = e->rhs && IsEventVar(e->rhs, types);
    if ((lhs_ev || rhs_ev) && !IsAllowedEventBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 std::format("binary operator {} is not allowed on event "
                             "variable",
                             TokenKindName(e->op)),
                 Subclause("15.5.5.3"));
    }
  }
  if (e->kind == ExprKind::kUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start,
               std::format("unary operator {} is not allowed on event variable",
                           TokenKindName(e->op)),
               Subclause("15.5.5.3"));
  }
  if (e->kind == ExprKind::kPostfixUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start,
               std::format("postfix operator {} is not allowed on event "
                           "variable",
                           TokenKindName(e->op)),
               Subclause("15.5.5.3"));
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
  CheckEventExpr(s->rhs, var_types_, diag_);
  CheckEventExpr(s->expr, var_types_, diag_);
  CheckEventExpr(s->condition, var_types_, diag_);
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForEventOps(sub); });
}

void Elaborator::ValidateEventOps(const ModuleDecl* decl) {
  ReportNonEventOperands(decl, var_types_, diag_);
  bool has_event = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kEvent) {
      has_event = true;
      break;
    }
  }
  if (!has_event) return;
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForEventOps(item->body);
    }
  }
}

}  // namespace delta
