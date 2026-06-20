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

// §20.16, Syntax 20-16 and Table 20-12: a PLA modeling system task is named
// $<array_type>$<logic>$<format>, where array_type is sync or async, logic is
// one of and/or/nand/nor, and format is array or plane. Matching a callee
// against those three dollar-separated components recognizes exactly the
// sixteen tasks the table enumerates and nothing else.
bool IsPlaSystemTask(std::string_view callee) {
  if (callee.empty() || callee.front() != '$') return false;
  std::string_view rest = callee.substr(1);
  auto take = [&rest]() -> std::string_view {
    auto pos = rest.find('$');
    std::string_view tok = rest.substr(0, pos);
    rest = pos == std::string_view::npos ? std::string_view{}
                                         : rest.substr(pos + 1);
    return tok;
  };
  std::string_view array_type = take();
  std::string_view logic = take();
  std::string_view format = take();
  if (!rest.empty()) return false;  // more than three components
  bool ok_type = array_type == "sync" || array_type == "async";
  bool ok_logic =
      logic == "and" || logic == "or" || logic == "nand" || logic == "nor";
  bool ok_format = format == "array" || format == "plane";
  return ok_type && ok_logic && ok_format;
}

// §20.16: "the output terms shall only be variables." The output-terms argument
// may be a single lvalue or a concatenation of them; flag every leaf whose base
// identifier names a net rather than a variable.
void CheckPlaOutputOperand(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements)
      CheckPlaOutputOperand(el, net_names, loc, diag);
    return;
  }
  auto base = LhsBaseName(e);
  if (!base.empty() && net_names.count(base) != 0) {
    diag.Error(loc,
               "output terms of a PLA modeling system task shall be variables, "
               "not nets");
  }
}

void CheckPlaOutputTermsExpr(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsPlaSystemTask(e->callee) &&
      e->args.size() >= 3 && e->args[2]) {
    CheckPlaOutputOperand(e->args[2], net_names, e->range.start, diag);
  }
  CheckPlaOutputTermsExpr(e->lhs, net_names, diag);
  CheckPlaOutputTermsExpr(e->rhs, net_names, diag);
  CheckPlaOutputTermsExpr(e->condition, net_names, diag);
  CheckPlaOutputTermsExpr(e->true_expr, net_names, diag);
  CheckPlaOutputTermsExpr(e->false_expr, net_names, diag);
  CheckPlaOutputTermsExpr(e->base, net_names, diag);
  CheckPlaOutputTermsExpr(e->index, net_names, diag);
  for (auto* a : e->args) CheckPlaOutputTermsExpr(a, net_names, diag);
  for (auto* el : e->elements) CheckPlaOutputTermsExpr(el, net_names, diag);
}

void CheckPlaOutputTermsStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckPlaOutputTermsExpr(s->condition, net_names, diag);
  CheckPlaOutputTermsExpr(s->lhs, net_names, diag);
  CheckPlaOutputTermsExpr(s->rhs, net_names, diag);
  CheckPlaOutputTermsExpr(s->expr, net_names, diag);
  CheckPlaOutputTermsExpr(s->var_init, net_names, diag);
  for (auto* sub : s->stmts) CheckPlaOutputTermsStmt(sub, net_names, diag);
  for (auto* sub : s->fork_stmts) CheckPlaOutputTermsStmt(sub, net_names, diag);
  CheckPlaOutputTermsStmt(s->then_branch, net_names, diag);
  CheckPlaOutputTermsStmt(s->else_branch, net_names, diag);
  CheckPlaOutputTermsStmt(s->body, net_names, diag);
  CheckPlaOutputTermsStmt(s->for_body, net_names, diag);
  for (auto* init : s->for_inits)
    CheckPlaOutputTermsStmt(init, net_names, diag);
  for (auto& ci : s->case_items)
    CheckPlaOutputTermsStmt(ci.body, net_names, diag);
}

}  // namespace

void Elaborator::ValidatePlaOutputTerms(const ModuleDecl* decl) {
  // §20.16: the output terms of a PLA modeling system task shall be variables,
  // never nets. Input terms may be nets or variables, so only the output-terms
  // argument is checked.
  for (const auto* item : decl->items) {
    if (item->body) CheckPlaOutputTermsStmt(item->body, net_names_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckPlaOutputTermsStmt(s, net_names_, diag_);
    CheckPlaOutputTermsExpr(item->init_expr, net_names_, diag_);
  }
}

namespace {

// §20.16.3: the constant-folded declaration ranges of a signal that may be
// named as a PLA memory or term, used to test the ascending-order requirement.
struct PlaDeclRanges {
  std::optional<int64_t> packed_left;
  std::optional<int64_t> packed_right;
  // Each unpacked dimension that folds to a constant [left:right] range.
  std::vector<std::pair<int64_t, int64_t>> unpacked;
};

using PlaRangeMap = std::unordered_map<std::string_view, PlaDeclRanges>;

// §20.16.3: "PLA input terms, output terms, and memory shall be specified in
// ascending order." A declared range is ascending when its left index is no
// greater than its right index; flag a memory or term whose declaration runs
// the other way. The check uses only the base identifier's declaration, so a
// term given as a concatenation of scalars or a range that does not fold to a
// constant is simply left unchecked.
void CheckPlaArgAscending(const Expr* arg, const PlaRangeMap& ranges,
                          bool check_unpacked, const char* message,
                          DiagEngine& diag) {
  if (!arg) return;
  auto base = LhsBaseName(arg);
  if (base.empty()) return;
  auto it = ranges.find(base);
  if (it == ranges.end()) return;
  const PlaDeclRanges& r = it->second;
  if (r.packed_left && r.packed_right && *r.packed_left > *r.packed_right) {
    diag.Error(arg->range.start, message);
    return;
  }
  if (check_unpacked) {
    for (const auto& dim : r.unpacked) {
      if (dim.first > dim.second) {
        diag.Error(arg->range.start, message);
        return;
      }
    }
  }
}

// §20.16.3: at every PLA system task call, check the memory (first argument)
// for ascending packed and unpacked ranges and the input/output term arguments
// for ascending packed ranges.
void CheckPlaAscendingExpr(const Expr* e, const PlaRangeMap& ranges,
                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsPlaSystemTask(e->callee)) {
    if (e->args.size() >= 1)
      CheckPlaArgAscending(
          e->args[0], ranges, /*check_unpacked=*/true,
          "the memory of a PLA modeling system task shall be declared in "
          "ascending order",
          diag);
    if (e->args.size() >= 2)
      CheckPlaArgAscending(
          e->args[1], ranges, /*check_unpacked=*/false,
          "the input terms of a PLA modeling system task shall be specified in "
          "ascending order",
          diag);
    if (e->args.size() >= 3)
      CheckPlaArgAscending(e->args[2], ranges, /*check_unpacked=*/false,
                           "the output terms of a PLA modeling system task "
                           "shall be specified in "
                           "ascending order",
                           diag);
  }
  CheckPlaAscendingExpr(e->lhs, ranges, diag);
  CheckPlaAscendingExpr(e->rhs, ranges, diag);
  CheckPlaAscendingExpr(e->condition, ranges, diag);
  CheckPlaAscendingExpr(e->true_expr, ranges, diag);
  CheckPlaAscendingExpr(e->false_expr, ranges, diag);
  CheckPlaAscendingExpr(e->base, ranges, diag);
  CheckPlaAscendingExpr(e->index, ranges, diag);
  for (auto* a : e->args) CheckPlaAscendingExpr(a, ranges, diag);
  for (auto* el : e->elements) CheckPlaAscendingExpr(el, ranges, diag);
}

void CheckPlaAscendingStmt(const Stmt* s, const PlaRangeMap& ranges,
                           DiagEngine& diag) {
  if (!s) return;
  CheckPlaAscendingExpr(s->condition, ranges, diag);
  CheckPlaAscendingExpr(s->lhs, ranges, diag);
  CheckPlaAscendingExpr(s->rhs, ranges, diag);
  CheckPlaAscendingExpr(s->expr, ranges, diag);
  CheckPlaAscendingExpr(s->var_init, ranges, diag);
  for (auto* sub : s->stmts) CheckPlaAscendingStmt(sub, ranges, diag);
  for (auto* sub : s->fork_stmts) CheckPlaAscendingStmt(sub, ranges, diag);
  CheckPlaAscendingStmt(s->then_branch, ranges, diag);
  CheckPlaAscendingStmt(s->else_branch, ranges, diag);
  CheckPlaAscendingStmt(s->body, ranges, diag);
  CheckPlaAscendingStmt(s->for_body, ranges, diag);
  for (auto* init : s->for_inits) CheckPlaAscendingStmt(init, ranges, diag);
  for (auto& ci : s->case_items) CheckPlaAscendingStmt(ci.body, ranges, diag);
}

// §20.16.3: fold a single declaration's packed and constant unpacked ranges
// into the PlaDeclRanges record used by the ascending-order check.
PlaDeclRanges CollectPlaDeclRanges(const ModuleItem* item) {
  PlaDeclRanges r;
  r.packed_left = ConstEvalInt(item->data_type.packed_dim_left);
  r.packed_right = ConstEvalInt(item->data_type.packed_dim_right);
  for (auto* dim : item->unpacked_dims) {
    if (dim && dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto l = ConstEvalInt(dim->lhs);
      auto rr = ConstEvalInt(dim->rhs);
      if (l && rr) r.unpacked.push_back({*l, *rr});
    }
  }
  return r;
}

}  // namespace

void Elaborator::ValidatePlaAscendingOrder(const ModuleDecl* decl) {
  // §20.16.3: PLA input terms, output terms, and memory shall be specified in
  // ascending order. Collect each signal's declared ranges first, then check
  // every PLA call that names one as its memory or as a term.
  PlaRangeMap ranges;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl &&
        item->kind != ModuleItemKind::kNetDecl)
      continue;
    ranges.emplace(item->name, CollectPlaDeclRanges(item));
  }
  if (ranges.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) CheckPlaAscendingStmt(item->body, ranges, diag_);
    for (auto* s : item->func_body_stmts)
      CheckPlaAscendingStmt(s, ranges, diag_);
    CheckPlaAscendingExpr(item->init_expr, ranges, diag_);
  }
}

namespace {

// §20.7.1: a single unpacked dimension is "variable-sized" when it is a dynamic
// array ([], stored as a null dimension), a queue ([$]), or a wildcard
// associative array ([*]) — the same classification §20.7 uses for a
// dynamically sized dimension.
bool DimIsVariableSized(const Expr* d) {
  if (d == nullptr) return true;
  return d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*");
}

using VarDimMap =
    std::unordered_map<std::string_view, const std::vector<Expr*>*>;

// §20.7.1: when a §20.7 query function is called as (v, n) on an array variable
// v with a constant dimension index n greater than 1, it is an error if the
// n-th dimension is variable-sized. The slowest-varying unpacked dimension is
// dimension 1, so unpacked_dims[n-1] names dimension n. Dimension 1 (or a query
// with no dimension argument) stays legal even when it is variable-sized, since
// a query on the outermost dynamic dimension still has a well-defined extent;
// an inner variable-sized dimension does not, because each element of the
// slower-varying dimension can hold a differently sized object. $dimensions and
// $unpacked_dimensions take no second argument, so they never reach this check.
void CheckArrayQueryOnVarDimExpr(const Expr* e, const VarDimMap& vars,
                                 DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      e->args.size() >= 2 && e->args[0] && e->args[1] &&
      e->args[0]->kind == ExprKind::kIdentifier &&
      e->args[1]->kind == ExprKind::kIntegerLiteral) {
    auto it = vars.find(e->args[0]->text);
    uint64_t n = e->args[1]->int_val;
    if (it != vars.end() && n > 1) {
      const std::vector<Expr*>& dims = *it->second;
      if (n <= dims.size() && DimIsVariableSized(dims[n - 1])) {
        diag.Error(e->range.start,
                   std::format("array query function '{}' cannot query "
                               "variable-sized dimension {} of array '{}'",
                               e->callee, n, e->args[0]->text));
      }
    }
  }
  CheckArrayQueryOnVarDimExpr(e->lhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->rhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->condition, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->true_expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->false_expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->base, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->index, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->index_end, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->repeat_count, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->with_expr, vars, diag);
  for (auto* a : e->args) CheckArrayQueryOnVarDimExpr(a, vars, diag);
  for (auto* el : e->elements) CheckArrayQueryOnVarDimExpr(el, vars, diag);
}

void CheckArrayQueryOnVarDimStmt(const Stmt* s, const VarDimMap& vars,
                                 DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnVarDimExpr(s->condition, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->lhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->rhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->delay, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->var_init, vars, diag);
  for (auto* sub : s->stmts) CheckArrayQueryOnVarDimStmt(sub, vars, diag);
  for (auto* sub : s->fork_stmts) CheckArrayQueryOnVarDimStmt(sub, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->then_branch, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->else_branch, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->body, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->for_body, vars, diag);
  for (auto* init : s->for_inits) CheckArrayQueryOnVarDimStmt(init, vars, diag);
  for (auto& ci : s->case_items)
    CheckArrayQueryOnVarDimStmt(ci.body, vars, diag);
}

}  // namespace

void Elaborator::ValidateArrayQueryOnVariableDim(const ModuleDecl* decl) {
  // Map every array variable in the module to its unpacked dimension list, then
  // reject any (v, n>1) query whose n-th dimension is variable-sized.
  VarDimMap vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->unpacked_dims.empty())
      vars.emplace(item->name, &item->unpacked_dims);
  }
  if (vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) CheckArrayQueryOnVarDimStmt(item->body, vars, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnVarDimStmt(s, vars, diag_);
    CheckArrayQueryOnVarDimExpr(item->init_expr, vars, diag_);
  }
}

namespace {

bool IsBitsCall(const Expr* e) {
  return e && e->kind == ExprKind::kSystemCall && e->callee == "$bits" &&
         e->args.size() == 1 && e->args[0];
}

// §20.6.2 (NC12, NC13): a bare identifier argument names either a dynamically
// sized typedef or an interface-class object; flag whichever applies.
void CheckBitsCallIdentArg(
    const Expr* call, const Expr* a,
    const std::unordered_set<std::string_view>& dyn_types,
    const std::unordered_set<std::string_view>& iface_vars, DiagEngine& diag) {
  if (dyn_types.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' cannot be applied directly to "
                           "dynamically sized type '{}'",
                           a->text));
  }
  if (iface_vars.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' shall not be applied to interface "
                           "class object '{}'",
                           a->text));
  }
}

// §20.6.2 (NC9): a call argument that names a function with a dynamically sized
// return type has no defined bit-stream size.
void CheckBitsCallFuncArg(const Expr* call, const Expr* a,
                          const std::unordered_set<std::string_view>& dyn_funcs,
                          DiagEngine& diag) {
  std::string_view name = a->callee;
  if (name.empty() && a->lhs && a->lhs->kind == ExprKind::kIdentifier)
    name = a->lhs->text;
  if (!name.empty() && dyn_funcs.count(name) != 0) {
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
                      const std::unordered_set<std::string_view>& dyn_types,
                      const std::unordered_set<std::string_view>& dyn_funcs,
                      const std::unordered_set<std::string_view>& iface_vars,
                      DiagEngine& diag) {
  if (a->kind == ExprKind::kIdentifier) {
    CheckBitsCallIdentArg(call, a, dyn_types, iface_vars, diag);
  } else if (a->kind == ExprKind::kCall) {
    CheckBitsCallFuncArg(call, a, dyn_funcs, diag);
  }
}

// §20.6.2: a single argument that is a bare identifier names either the
// dynamically sized typedef itself (NC12) or an interface-class object (NC13);
// in either case there is no defined bit-stream size.
void CheckBitsCallExpr(const Expr* e,
                       const std::unordered_set<std::string_view>& dyn_types,
                       const std::unordered_set<std::string_view>& dyn_funcs,
                       const std::unordered_set<std::string_view>& iface_vars,
                       DiagEngine& diag) {
  if (!e) return;
  if (IsBitsCall(e)) {
    CheckBitsCallArg(e, e->args[0], dyn_types, dyn_funcs, iface_vars, diag);
  }
  CheckBitsCallExpr(e->lhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->rhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->condition, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->true_expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->false_expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->base, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->index, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->index_end, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->repeat_count, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->with_expr, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* a : e->args)
    CheckBitsCallExpr(a, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* el : e->elements)
    CheckBitsCallExpr(el, dyn_types, dyn_funcs, iface_vars, diag);
}

void CheckBitsCallStmt(const Stmt* s,
                       const std::unordered_set<std::string_view>& dyn_types,
                       const std::unordered_set<std::string_view>& dyn_funcs,
                       const std::unordered_set<std::string_view>& iface_vars,
                       DiagEngine& diag) {
  if (!s) return;
  CheckBitsCallExpr(s->condition, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->lhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->rhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->delay, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->var_init, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* sub : s->stmts)
    CheckBitsCallStmt(sub, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* sub : s->fork_stmts)
    CheckBitsCallStmt(sub, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->then_branch, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->else_branch, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->body, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->for_body, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* init : s->for_inits)
    CheckBitsCallStmt(init, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto& ci : s->case_items)
    CheckBitsCallStmt(ci.body, dyn_types, dyn_funcs, iface_vars, diag);
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

  for (const auto* item : decl->items) {
    if (item->body)
      CheckBitsCallStmt(item->body, dyn_types, dyn_funcs, iface_vars, diag_);
    for (auto* s : item->func_body_stmts)
      CheckBitsCallStmt(s, dyn_types, dyn_funcs, iface_vars, diag_);
    CheckBitsCallExpr(item->init_expr, dyn_types, dyn_funcs, iface_vars, diag_);
  }
}

static bool IsConstantBitSelect(const Expr* e) {
  if (e->is_part_select_plus || e->is_part_select_minus) return false;
  if (e->index && e->index_end) return true;
  if (e->index && !e->index_end) {
    return ConstEvalInt(e->index).has_value();
  }
  return true;
}

static bool IsConstantSelect(const Expr* e) {
  if (!e) return true;
  if (e->kind == ExprKind::kIdentifier) return true;
  if (e->kind == ExprKind::kSelect) return IsConstantBitSelect(e);
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) {
      if (!IsConstantSelect(elem)) return false;
    }
    return true;
  }
  return true;
}

void Elaborator::ValidateContAssignConstSelect(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    if (!IsConstantSelect(item->assign_lhs)) {
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

static bool ExprContainsHierRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (ExprContainsHierRef(e->lhs)) return true;
  if (ExprContainsHierRef(e->rhs)) return true;
  if (ExprContainsHierRef(e->condition)) return true;
  if (ExprContainsHierRef(e->true_expr)) return true;
  if (ExprContainsHierRef(e->false_expr)) return true;
  for (auto* elem : e->elements) {
    if (ExprContainsHierRef(elem)) return true;
  }
  for (auto* arg : e->args) {
    if (ExprContainsHierRef(arg)) return true;
  }
  return false;
}

namespace {

// Flag the elaborated parameter overrides in decl->params whose value contains
// a hierarchical reference.
void CheckParamMapHierRefs(const ModuleDecl* decl, DiagEngine& diag) {
  for (const auto& [pname, pval] : decl->params) {
    if (!pval) continue;
    if (ExprContainsHierRef(pval)) {
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
                           DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind != DataTypeKind::kImplicit)
    return;
  if (!item->init_expr) {
    diag.Error(
        item->loc,
        std::format("value parameter '{}' has no default value", item->name));
    return;
  }

  if (ExprContainsHierRef(item->init_expr)) {
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
    ValidateOneValueParam(item, param_scope, diag_);
  }

  CheckParamMapHierRefs(decl, diag_);
}

}  // namespace delta
