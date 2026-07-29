#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §20.6.2 (NC9, NC12, NC13): the names in a module that have no defined
// bit-stream size and therefore may not be enclosed by '$bits': dynamically
// sized typedefs (NC12), functions whose return type is such a typedef (NC9),
// and objects whose type is an interface class (NC13, see §8.26).
struct BitsDynamicNames {
  const std::unordered_set<std::string_view>& dyn_types;
  const std::unordered_set<std::string_view>& dyn_funcs;
  const std::unordered_set<std::string_view>& iface_vars;
};

bool IsBitsCall(const Expr* e) {
  return e && e->kind == ExprKind::kSystemCall && e->callee == "$bits" &&
         e->args.size() == 1 && e->args[0];
}

// §20.6.2 (NC12, NC13): a bare identifier argument names either a dynamically
// sized typedef or an interface-class object; flag whichever applies.
void CheckBitsCallIdentArg(const Expr* call, const Expr* a,
                           const BitsDynamicNames& names, DiagEngine& diag) {
  if (names.dyn_types.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' cannot be applied directly to "
                           "dynamically sized type '{}'",
                           a->text));
  }
  if (names.iface_vars.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' shall not be applied to interface "
                           "class object '{}'",
                           a->text));
  }
}

// §20.6.2 (NC9): a call argument that names a function with a dynamically sized
// return type has no defined bit-stream size.
void CheckBitsCallFuncArg(const Expr* call, const Expr* a,
                          const BitsDynamicNames& names, DiagEngine& diag) {
  std::string_view name = a->callee;
  if (name.empty() && a->lhs && a->lhs->kind == ExprKind::kIdentifier)
    name = a->lhs->text;
  if (!name.empty() && names.dyn_funcs.count(name) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' shall not enclose function '{}' "
                           "whose return type is dynamically sized",
                           name));
  }
}

// §20.6.2: report the restricted forms of a confirmed $bits call: a bare
// identifier naming a dynamically sized typedef (NC12) or an interface-class
// object (NC13), or a call to a function with a dynamically sized return type
// (NC9).
void CheckBitsCallArg(const Expr* call, const Expr* a,
                      const BitsDynamicNames& names, DiagEngine& diag) {
  if (a->kind == ExprKind::kIdentifier) {
    CheckBitsCallIdentArg(call, a, names, diag);
  } else if (a->kind == ExprKind::kCall) {
    CheckBitsCallFuncArg(call, a, names, diag);
  }
}

// §20.6.2: a single argument that is a bare identifier names either the
// dynamically sized typedef itself (NC12) or an interface-class object (NC13);
// in either case there is no defined bit-stream size.
void CheckBitsCallExpr(const Expr* e, const BitsDynamicNames& names,
                       DiagEngine& diag) {
  if (!e) return;
  if (IsBitsCall(e)) {
    CheckBitsCallArg(e, e->args[0], names, diag);
  }
  CheckBitsCallExpr(e->lhs, names, diag);
  CheckBitsCallExpr(e->rhs, names, diag);
  CheckBitsCallExpr(e->condition, names, diag);
  CheckBitsCallExpr(e->true_expr, names, diag);
  CheckBitsCallExpr(e->false_expr, names, diag);
  CheckBitsCallExpr(e->base, names, diag);
  CheckBitsCallExpr(e->index, names, diag);
  CheckBitsCallExpr(e->index_end, names, diag);
  CheckBitsCallExpr(e->repeat_count, names, diag);
  CheckBitsCallExpr(e->with_expr, names, diag);
  for (auto* a : e->args) CheckBitsCallExpr(a, names, diag);
  for (auto* el : e->elements) CheckBitsCallExpr(el, names, diag);
}

void CheckBitsCallStmt(const Stmt* s, const BitsDynamicNames& names,
                       DiagEngine& diag) {
  if (!s) return;
  CheckBitsCallExpr(s->condition, names, diag);
  CheckBitsCallExpr(s->lhs, names, diag);
  CheckBitsCallExpr(s->rhs, names, diag);
  CheckBitsCallExpr(s->expr, names, diag);
  CheckBitsCallExpr(s->delay, names, diag);
  CheckBitsCallExpr(s->var_init, names, diag);
  for (auto* sub : s->stmts) CheckBitsCallStmt(sub, names, diag);
  for (auto* sub : s->fork_stmts) CheckBitsCallStmt(sub, names, diag);
  CheckBitsCallStmt(s->then_branch, names, diag);
  CheckBitsCallStmt(s->else_branch, names, diag);
  CheckBitsCallStmt(s->body, names, diag);
  CheckBitsCallStmt(s->for_body, names, diag);
  for (auto* init : s->for_inits) CheckBitsCallStmt(init, names, diag);
  for (auto& ci : s->case_items) CheckBitsCallStmt(ci.body, names, diag);
}

// §20.6.2 (NC12): the typedefs in the module whose declared unpacked dimensions
// are dynamically sized.
std::unordered_set<std::string_view> CollectDynamicTypes(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  return dyn_types;
}

// §20.6.2 (NC9): the functions in the module whose return type names one of the
// dynamically sized typedefs.
std::unordered_set<std::string_view> CollectDynamicFuncs(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& dyn_types) {
  std::unordered_set<std::string_view> dyn_funcs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl) continue;
    if (item->return_type.kind == DataTypeKind::kNamed &&
        dyn_types.count(item->return_type.type_name) != 0) {
      dyn_funcs.insert(item->name);
    }
  }
  return dyn_funcs;
}

}  // namespace

void Elaborator::ValidateBitsCallRestrictions(const ModuleDecl* decl) {
  // §20.6.2: $bits cannot be used directly on a dynamically sized type
  // identifier (NC12), cannot enclose a function whose return type is
  // dynamically sized (NC9), and cannot be applied to an object whose type is
  // an interface class (NC13, see §8.26).
  std::unordered_set<std::string_view> dyn_types = CollectDynamicTypes(decl);
  std::unordered_set<std::string_view> dyn_funcs =
      CollectDynamicFuncs(decl, dyn_types);
  std::unordered_set<std::string_view> iface_vars;
  for (const auto& [vname, cls_name] : class_var_types_) {
    const auto* cls = FindClassDecl(cls_name, unit_);
    if (cls && cls->is_interface) iface_vars.insert(vname);
  }
  if (dyn_types.empty() && dyn_funcs.empty() && iface_vars.empty()) return;

  const BitsDynamicNames kNames{dyn_types, dyn_funcs, iface_vars};
  for (const auto* item : decl->items) {
    if (item->body) CheckBitsCallStmt(item->body, kNames, diag_);
    for (auto* s : item->func_body_stmts) CheckBitsCallStmt(s, kNames, diag_);
    CheckBitsCallExpr(item->init_expr, kNames, diag_);
  }
}

static bool IsConstantBitSelect(const Expr* e, const ScopeMap& scope) {
  if (e->is_part_select_plus || e->is_part_select_minus) return false;
  if (e->index && e->index_end) return true;
  if (e->index && !e->index_end) {
    return ConstEvalInt(e->index, scope).has_value();
  }
  return true;
}

static bool IsConstantSelect(const Expr* e, const ScopeMap& scope) {
  if (!e) return true;
  if (e->kind == ExprKind::kIdentifier) return true;
  if (e->kind == ExprKind::kSelect) return IsConstantBitSelect(e, scope);
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) {
      if (!IsConstantSelect(elem, scope)) return false;
    }
    return true;
  }
  return true;
}

// §11.2.1 counts parameters among the operands a constant expression is made
// of, so an index naming one is constant and the select it indexes is a
// constant select. This runs on the module declaration rather than the
// elaborated module, so the values come from the declaration's own parameter
// items, each folded in the scope its predecessors established -- a parameter
// may be defined in terms of an earlier one. A parameter whose value does not
// fold here is simply absent, leaving the index as non-constant as it was.
static ScopeMap DeclParamScope(const ModuleDecl* decl) {
  ScopeMap scope;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl || !item->init_expr) continue;
    if (auto value = ConstEvalInt(item->init_expr, scope)) {
      scope[item->name] = *value;
    }
  }
  return scope;
}

void Elaborator::ValidateContAssignConstSelect(const ModuleDecl* decl) {
  ScopeMap scope = DeclParamScope(decl);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    if (!IsConstantSelect(item->assign_lhs, scope)) {
      diag_.Error(item->loc,
                  "continuous assignment left-hand side requires a "
                  "constant select expression");
    }
  }
}

namespace {

// Reports whether an expression names any of the given run-time signals
// (module variables or nets). A part-select bound that does so cannot be a
// constant expression.
bool ExprNamesSignal(const Expr* e,
                     const std::unordered_set<std::string_view>& signals);

// Whether any of an expression's scalar (single-pointer) child slots names one
// of the given run-time signals.
bool ScalarChildNamesSignal(
    const Expr* e, const std::unordered_set<std::string_view>& signals) {
  return ExprNamesSignal(e->lhs, signals) || ExprNamesSignal(e->rhs, signals) ||
         ExprNamesSignal(e->condition, signals) ||
         ExprNamesSignal(e->true_expr, signals) ||
         ExprNamesSignal(e->false_expr, signals) ||
         ExprNamesSignal(e->base, signals) ||
         ExprNamesSignal(e->index, signals) ||
         ExprNamesSignal(e->index_end, signals) ||
         ExprNamesSignal(e->with_expr, signals) ||
         ExprNamesSignal(e->repeat_count, signals);
}

bool ExprNamesSignal(const Expr* e,
                     const std::unordered_set<std::string_view>& signals) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return signals.count(e->text) > 0;
  if (ScalarChildNamesSignal(e, signals)) return true;
  for (const auto* a : e->args)
    if (ExprNamesSignal(a, signals)) return true;
  for (const auto* el : e->elements)
    if (ExprNamesSignal(el, signals)) return true;
  return false;
}

struct PartSelectBoundsCtx {
  const std::unordered_set<std::string_view>& signals;
  // Packed vectors (no unpacked dimensions) whose declared range folds to a
  // constant, keyed by name and mapping to (left, right) bounds.
  const std::unordered_map<std::string_view, std::pair<int64_t, int64_t>>&
      ranges;
  DiagEngine& diag;
};

// §11.5.1: check one qualifying non-indexed part-select (vect[msb:lsb] on a
// simple packed vector) for constant bounds and correct index ordering.
void CheckOnePartSelectBounds(const Expr* e, const PartSelectBoundsCtx& ctx) {
  if (ExprNamesSignal(e->index, ctx.signals) ||
      ExprNamesSignal(e->index_end, ctx.signals)) {
    ctx.diag.Error(e->range.start,
                   "non-indexed part-select bounds shall be constant "
                   "expressions");
    return;
  }
  auto msb = ConstEvalInt(e->index);
  auto lsb = ConstEvalInt(e->index_end);
  if (!msb || !lsb) return;
  const auto& range = ctx.ranges.at(e->base->text);
  bool descending = range.first >= range.second;
  // The first index shall name a more significant bit than the second. For a
  // descending declaration the more significant bit has the larger index; for
  // an ascending one it has the smaller index. Equal indices (a one-bit
  // part-select) are permitted.
  bool reversed = descending ? (*msb < *lsb) : (*msb > *lsb);
  if (reversed)
    ctx.diag.Error(e->range.start,
                   "part-select's first index must address a more "
                   "significant bit than its second index");
}

void CheckPartSelectBoundsExpr(const Expr* e, const PartSelectBoundsCtx& ctx) {
  if (!e) return;
  // Only a non-indexed part-select (vect[msb:lsb], not an indexed +:/-: form
  // and not a plain bit-select) on a simple packed-vector reference falls under
  // these §11.5.1 rules.
  if (e->kind == ExprKind::kSelect && e->index && e->index_end &&
      !e->is_part_select_plus && !e->is_part_select_minus && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      ctx.ranges.count(e->base->text)) {
    CheckOnePartSelectBounds(e, ctx);
  }
  CheckPartSelectBoundsExpr(e->lhs, ctx);
  CheckPartSelectBoundsExpr(e->rhs, ctx);
  CheckPartSelectBoundsExpr(e->condition, ctx);
  CheckPartSelectBoundsExpr(e->true_expr, ctx);
  CheckPartSelectBoundsExpr(e->false_expr, ctx);
  CheckPartSelectBoundsExpr(e->base, ctx);
  CheckPartSelectBoundsExpr(e->index, ctx);
  CheckPartSelectBoundsExpr(e->index_end, ctx);
  CheckPartSelectBoundsExpr(e->with_expr, ctx);
  CheckPartSelectBoundsExpr(e->repeat_count, ctx);
  for (const auto* a : e->args) CheckPartSelectBoundsExpr(a, ctx);
  for (const auto* el : e->elements) CheckPartSelectBoundsExpr(el, ctx);
}

void CheckPartSelectBoundsStmt(const Stmt* s, const PartSelectBoundsCtx& ctx) {
  if (!s) return;
  CheckPartSelectBoundsExpr(s->lhs, ctx);
  CheckPartSelectBoundsExpr(s->rhs, ctx);
  CheckPartSelectBoundsExpr(s->expr, ctx);
  CheckPartSelectBoundsExpr(s->condition, ctx);
  for (const auto* c : s->stmts) CheckPartSelectBoundsStmt(c, ctx);
  CheckPartSelectBoundsStmt(s->then_branch, ctx);
  CheckPartSelectBoundsStmt(s->else_branch, ctx);
  CheckPartSelectBoundsStmt(s->body, ctx);
  for (const auto* fi : s->for_inits) CheckPartSelectBoundsStmt(fi, ctx);
  CheckPartSelectBoundsStmt(s->for_body, ctx);
  for (const auto* fs : s->for_steps) CheckPartSelectBoundsStmt(fs, ctx);
  CheckPartSelectBoundsExpr(s->for_cond, ctx);
  for (const auto& ci : s->case_items) CheckPartSelectBoundsStmt(ci.body, ctx);
  for (const auto* fs : s->fork_stmts) CheckPartSelectBoundsStmt(fs, ctx);
}

}  // namespace

void Elaborator::ValidatePartSelectBounds(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> signals;
  std::unordered_map<std::string_view, std::pair<int64_t, int64_t>> ranges;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl &&
        item->kind != ModuleItemKind::kNetDecl)
      continue;
    signals.insert(item->name);
    // Record a range only for a plain packed vector whose bounds are constant,
    // so the ordering check never fires on an unpacked array slice or on a
    // parameterized range it cannot resolve.
    if (item->unpacked_dims.empty()) {
      auto left = ConstEvalInt(item->data_type.packed_dim_left);
      auto right = ConstEvalInt(item->data_type.packed_dim_right);
      if (left && right) ranges[item->name] = {*left, *right};
    }
  }
  if (ranges.empty()) return;

  PartSelectBoundsCtx ctx{signals, ranges, diag_};
  for (const auto* item : decl->items) {
    CheckPartSelectBoundsExpr(item->assign_lhs, ctx);
    CheckPartSelectBoundsExpr(item->assign_rhs, ctx);
    CheckPartSelectBoundsExpr(item->init_expr, ctx);
    CheckPartSelectBoundsStmt(item->body, ctx);
    for (const auto* s : item->func_body_stmts)
      CheckPartSelectBoundsStmt(s, ctx);
  }
}

void Elaborator::ValidateSpecparamInParams(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    if (!item->init_expr) continue;
    for (const auto& sp : specparam_names_) {
      if (ExprContainsIdent(item->init_expr, sp)) {
        diag_.Error(item->loc,
                    std::format("parameter references specparam '{}'", sp));
        break;
      }
    }
  }
}

namespace {

// §6.20.5: flag a single declaration range expression that references any
// specify parameter.
void CheckSpecparamInRange(
    const Expr* range, SourceLoc loc,
    const std::unordered_set<std::string_view>& specparam_names,
    DiagEngine& diag) {
  if (!range) return;
  for (const auto& sp : specparam_names) {
    if (ExprContainsIdent(range, sp)) {
      diag.Error(loc, std::format("specparam '{}' may not appear in a "
                                  "declaration range specification",
                                  sp));
      break;
    }
  }
}

// §6.20.5: check every packed and unpacked dimension expression of one net or
// variable declaration for a specparam reference.
void CheckDeclRangesForSpecparam(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& specparam_names,
    DiagEngine& diag) {
  CheckSpecparamInRange(item->data_type.packed_dim_left, item->loc,
                        specparam_names, diag);
  CheckSpecparamInRange(item->data_type.packed_dim_right, item->loc,
                        specparam_names, diag);
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    CheckSpecparamInRange(left, item->loc, specparam_names, diag);
    CheckSpecparamInRange(right, item->loc, specparam_names, diag);
  }
  for (const auto* dim : item->unpacked_dims) {
    CheckSpecparamInRange(dim, item->loc, specparam_names, diag);
  }
}

}  // namespace

void Elaborator::ValidateSpecparamInDeclRange(const ModuleDecl* decl) {
  if (specparam_names_.empty()) return;

  // §6.20.5: a specify parameter is reserved for timing/delay values and may
  // not participate in the range specification of a declaration. Flag any
  // packed or unpacked dimension expression of a net or variable declaration
  // that references a specparam.
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kNetDecl &&
        item->kind != ModuleItemKind::kVarDecl)
      continue;
    CheckDeclRangesForSpecparam(item, specparam_names_, diag_);
  }
}

// §11.2.1/§23.8: a hierarchical reference whose target is a parameter is a
// legal constant-expression operand. `base.member` is such a reference when a
// module named `base` declares `member` as a parameter (an upward or
// named-module reference to a constant). References to nets/variables (e.g. a
// child instance's signal, `s.x`) are not constants and remain forbidden.
static bool MemberAccessRefersToModuleParam(const CompilationUnit* unit,
                                            const Expr* e) {
  if (unit == nullptr || e->is_scope_resolution) return false;
  if (!e->lhs || e->lhs->kind != ExprKind::kIdentifier) return false;
  if (!e->rhs || e->rhs->kind != ExprKind::kIdentifier) return false;
  for (const auto* m : unit->modules) {
    if (m->name != e->lhs->text) continue;
    for (const auto* item : m->items) {
      if (item->kind == ModuleItemKind::kParamDecl &&
          item->name == e->rhs->text) {
        return true;
      }
    }
  }
  return false;
}

// §8.23: a class scope resolution `Class::PARAM` whose target is a class value
// parameter or local parameter is a legal constant-expression operand, not a
// hierarchical reference. (A class parameter is a public constant of the
// class.)
// §8.25: whether a class declares `name` as a parameter -- either a body
// parameter/localparam member or one of its #() parameter ports.
static bool ClassDeclaresParam(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param && m->name == name)
      return true;
  }
  for (const auto& [pname, pexpr] : cls->params) {
    (void)pexpr;
    if (pname == name) return true;
  }
  return false;
}

static bool ScopeResolutionRefersToClassParam(const CompilationUnit* unit,
                                              const Expr* e) {
  if (unit == nullptr || !e->is_scope_resolution) return false;
  if (!e->lhs || e->lhs->kind != ExprKind::kIdentifier) return false;
  if (!e->rhs || e->rhs->kind != ExprKind::kIdentifier) return false;
  for (const auto* cls : unit->classes) {
    if (cls->name != e->lhs->text) continue;
    if (ClassDeclaresParam(cls, e->rhs->text)) return true;
  }
  return false;
}

static bool ExprContainsHierRef(const Expr* e, const CompilationUnit* unit);

// True when any expression of `list` contains a hierarchical reference.
static bool AnyExprContainsHierRef(const std::vector<Expr*>& list,
                                   const CompilationUnit* unit) {
  for (auto* sub : list) {
    if (ExprContainsHierRef(sub, unit)) return true;
  }
  return false;
}

static bool ExprContainsHierRef(const Expr* e, const CompilationUnit* unit) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    if (MemberAccessRefersToModuleParam(unit, e)) return false;
    if (ScopeResolutionRefersToClassParam(unit, e)) return false;
    return true;
  }
  for (const Expr* sub :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr}) {
    if (ExprContainsHierRef(sub, unit)) return true;
  }
  return AnyExprContainsHierRef(e->elements, unit) ||
         AnyExprContainsHierRef(e->args, unit);
}

namespace {

// Flag the elaborated parameter overrides in decl->params whose value contains
// a hierarchical reference.
void CheckParamMapHierRefs(const ModuleDecl* decl, const CompilationUnit* unit,
                           DiagEngine& diag) {
  for (const auto& [pname, pval] : decl->params) {
    if (!pval) continue;
    if (ExprContainsHierRef(pval, unit)) {
      diag.Error(pval->range.start,
                 std::format("parameter '{}' value contains a hierarchical "
                             "reference",
                             pname));
    }
  }
}

// Validate one parameter declaration item: it must carry a default value, its
// value may not contain a hierarchical reference, and a localparam initialized
// with an assignment pattern must be a constant expression in param_scope.
void ValidateOneValueParam(const ModuleItem* item, const ScopeMap& param_scope,
                           const CompilationUnit* unit, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind != DataTypeKind::kImplicit)
    return;
  if (!item->init_expr) {
    diag.Error(
        item->loc,
        std::format("value parameter '{}' has no default value", item->name));
    return;
  }

  if (ExprContainsHierRef(item->init_expr, unit)) {
    diag.Error(item->loc,
               std::format("parameter '{}' value contains a hierarchical "
                           "reference",
                           item->name));
  }

  if (item->is_localparam &&
      item->init_expr->kind == ExprKind::kAssignmentPattern &&
      !IsConstantExpr(item->init_expr, param_scope)) {
    diag.Error(item->loc,
               std::format("localparam '{}' initializer is not a constant "
                           "expression",
                           item->name));
  }
}

}  // namespace

void Elaborator::ValidateValueParams(const ModuleDecl* decl,
                                     const RtlirModule* mod) {
  ScopeMap param_scope = BuildParamScope(mod);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    ValidateOneValueParam(item, param_scope, unit_, diag_);
  }

  CheckParamMapHierRefs(decl, unit_, diag_);
}

}  // namespace delta
