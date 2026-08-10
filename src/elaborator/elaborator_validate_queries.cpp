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
               "not nets",
               Subclause("20.16"));
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

// §21.3.3, Syntax 21-6: the string-formatting output tasks whose first
// argument is the variable receiving the formatted result. $sformatf is
// deliberately excluded — it returns the result as its function value and
// takes no output variable.
bool IsStringOutputTask(std::string_view callee) {
  return callee == "$swrite" || callee == "$swriteb" || callee == "$swriteh" ||
         callee == "$swriteo" || callee == "$sformat";
}

// §21.3.3: "The first argument to $swrite shall be a variable of integral,
// unpacked array of byte, or string data types." (The same output-variable
// rule governs $sformat's first argument.) A real-valued destination has no
// character representation, so it is the closest illegal form of that
// requirement and is rejected here. Other declared kinds (vectors, byte, enum,
// string, packed structs) are left alone to avoid false positives.
void CheckStringOutputTarget(const Expr* e, const TypeMap& types,
                             DiagEngine& diag) {
  if (e == nullptr || e->args.empty() || e->args[0] == nullptr) return;
  auto base = LhsBaseName(e->args[0]);
  if (base.empty()) return;
  auto it = types.find(base);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start,
               "the output variable of $swrite/$sformat shall be of an "
               "integral, unpacked array of byte, or string type, not real",
               Subclause("21.3.3"));
  }
}

void CheckStringOutputTargetsExpr(const Expr* e, const TypeMap& types,
                                  DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && IsStringOutputTask(e->callee))
    CheckStringOutputTarget(e, types, diag);
  CheckStringOutputTargetsExpr(e->lhs, types, diag);
  CheckStringOutputTargetsExpr(e->rhs, types, diag);
  CheckStringOutputTargetsExpr(e->condition, types, diag);
  CheckStringOutputTargetsExpr(e->true_expr, types, diag);
  CheckStringOutputTargetsExpr(e->false_expr, types, diag);
  CheckStringOutputTargetsExpr(e->base, types, diag);
  CheckStringOutputTargetsExpr(e->index, types, diag);
  for (auto* a : e->args) CheckStringOutputTargetsExpr(a, types, diag);
  for (auto* el : e->elements) CheckStringOutputTargetsExpr(el, types, diag);
}

void CheckStringOutputTargetsStmt(const Stmt* s, const TypeMap& types,
                                  DiagEngine& diag) {
  if (s == nullptr) return;
  CheckStringOutputTargetsExpr(s->condition, types, diag);
  CheckStringOutputTargetsExpr(s->lhs, types, diag);
  CheckStringOutputTargetsExpr(s->rhs, types, diag);
  CheckStringOutputTargetsExpr(s->expr, types, diag);
  CheckStringOutputTargetsExpr(s->var_init, types, diag);
  for (auto* sub : s->stmts) CheckStringOutputTargetsStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts)
    CheckStringOutputTargetsStmt(sub, types, diag);
  CheckStringOutputTargetsStmt(s->then_branch, types, diag);
  CheckStringOutputTargetsStmt(s->else_branch, types, diag);
  CheckStringOutputTargetsStmt(s->body, types, diag);
  CheckStringOutputTargetsStmt(s->for_body, types, diag);
  for (auto* init : s->for_inits)
    CheckStringOutputTargetsStmt(init, types, diag);
  for (auto& ci : s->case_items)
    CheckStringOutputTargetsStmt(ci.body, types, diag);
}

}  // namespace

void Elaborator::ValidateStringOutputTaskTargets(const ModuleDecl* decl) {
  // §21.3.3: the destination variable of $swrite/$swriteb/$swriteh/$swriteo and
  // $sformat shall be an integral, unpacked-array-of-byte, or string type; a
  // real destination is rejected.
  for (const auto* item : decl->items) {
    if (item->body) CheckStringOutputTargetsStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckStringOutputTargetsStmt(s, var_types_, diag_);
    CheckStringOutputTargetsExpr(item->init_expr, var_types_, diag_);
  }
}

namespace {

// §20.9, Syntax 20-10: the five bit-vector system functions -- $countbits and
// the derived $countones, $onehot, $onehot0, and $isunknown.
bool IsBitVectorFunction(std::string_view callee) {
  return callee == "$countbits" || callee == "$countones" ||
         callee == "$onehot" || callee == "$onehot0" || callee == "$isunknown";
}

// §20.9: the expression argument to $countbits (and, by the same rule, to each
// of the related functions) shall be of a bit-stream type. A real, event,
// chandle, or virtual-interface operand is not a bit-stream type; when the
// leading argument names such a variable, reject it. The control_bit arguments
// to $countbits (args[1..]) are 1-bit logic values, not the expression operand,
// so only the first argument carries this restriction.
void CheckBitVectorFunctionArg(const Expr* call, const TypeMap& types,
                               DiagEngine& diag) {
  // §20.9, Syntax 20-10: list_of_control_bits is non-empty, so $countbits shall
  // carry at least one control_bit after the expression argument. A call with
  // only the expression (or none at all) does not match the grammar.
  if (call->callee == "$countbits" && call->args.size() < 2) {
    diag.Error(call->range.start,
               "'$countbits' requires at least one control_bit argument",
               Subclause("20.9"));
    return;
  }
  if (call->args.empty() || call->args[0] == nullptr) return;
  auto base = LhsBaseName(call->args[0]);
  if (base.empty()) return;
  auto it = types.find(base);
  if (it == types.end()) return;
  auto k = it->second;
  if (IsRealType(k) || k == DataTypeKind::kEvent ||
      k == DataTypeKind::kChandle || k == DataTypeKind::kVirtualInterface) {
    diag.Error(call->range.start,
               std::format("the expression argument to '{}' shall be of a "
                           "bit-stream type",
                           call->callee),
               Subclause("20.9"));
  }
}

void CheckBitVectorArgExpr(const Expr* e, const TypeMap& types,
                           DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && IsBitVectorFunction(e->callee))
    CheckBitVectorFunctionArg(e, types, diag);
  CheckBitVectorArgExpr(e->lhs, types, diag);
  CheckBitVectorArgExpr(e->rhs, types, diag);
  CheckBitVectorArgExpr(e->condition, types, diag);
  CheckBitVectorArgExpr(e->true_expr, types, diag);
  CheckBitVectorArgExpr(e->false_expr, types, diag);
  CheckBitVectorArgExpr(e->base, types, diag);
  CheckBitVectorArgExpr(e->index, types, diag);
  for (auto* a : e->args) CheckBitVectorArgExpr(a, types, diag);
  for (auto* el : e->elements) CheckBitVectorArgExpr(el, types, diag);
}

void CheckBitVectorArgStmt(const Stmt* s, const TypeMap& types,
                           DiagEngine& diag) {
  if (s == nullptr) return;
  CheckBitVectorArgExpr(s->condition, types, diag);
  CheckBitVectorArgExpr(s->lhs, types, diag);
  CheckBitVectorArgExpr(s->rhs, types, diag);
  CheckBitVectorArgExpr(s->expr, types, diag);
  CheckBitVectorArgExpr(s->var_init, types, diag);
  for (auto* sub : s->stmts) CheckBitVectorArgStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckBitVectorArgStmt(sub, types, diag);
  CheckBitVectorArgStmt(s->then_branch, types, diag);
  CheckBitVectorArgStmt(s->else_branch, types, diag);
  CheckBitVectorArgStmt(s->body, types, diag);
  CheckBitVectorArgStmt(s->for_body, types, diag);
  for (auto* init : s->for_inits) CheckBitVectorArgStmt(init, types, diag);
  for (auto& ci : s->case_items) CheckBitVectorArgStmt(ci.body, types, diag);
}

}  // namespace

void Elaborator::ValidateBitVectorFunctionArgs(const ModuleDecl* decl) {
  // §20.9: the expression argument to the bit-vector functions ($countbits,
  // $countones, $onehot, $onehot0, $isunknown) shall be of a bit-stream type;
  // reject a statically recognizable non-bit-stream operand (a real, event,
  // chandle, or virtual interface).
  for (const auto* item : decl->items) {
    if (item->body) CheckBitVectorArgStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckBitVectorArgStmt(s, var_types_, diag_);
    CheckBitVectorArgExpr(item->init_expr, var_types_, diag_);
    // A continuous assignment is another place these functions may appear.
    CheckBitVectorArgExpr(item->assign_rhs, var_types_, diag_);
  }
}

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
  // A single bit-select (e.g. b[0]) names exactly one term, so there is no
  // term ordering to violate -- the declared range direction of the base
  // vector is irrelevant. Only a whole-vector term carries an order here.
  if (arg->kind == ExprKind::kSelect && arg->index && !arg->index_end &&
      !arg->is_part_select_plus && !arg->is_part_select_minus) {
    return;
  }
  auto base = LhsBaseName(arg);
  if (base.empty()) return;
  auto it = ranges.find(base);
  if (it == ranges.end()) return;
  const PlaDeclRanges& r = it->second;
  if (r.packed_left && r.packed_right && *r.packed_left > *r.packed_right) {
    diag.Error(arg->range.start, message, Subclause("20.16.3"));
    return;
  }
  if (check_unpacked) {
    for (const auto& dim : r.unpacked) {
      if (dim.first > dim.second) {
        diag.Error(arg->range.start, message, Subclause("20.16.3"));
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
// into the PlaDeclRanges record used by the ascending-order check. The range
// bounds are §11.2.1 constant expressions, so they are folded in the module's
// parameter scope: a parameter- or localparam-valued bound resolves the same
// way an integer literal does.
PlaDeclRanges CollectPlaDeclRanges(const ModuleItem* item,
                                   const ScopeMap& scope) {
  PlaDeclRanges r;
  r.packed_left = ConstEvalInt(item->data_type.packed_dim_left, scope);
  r.packed_right = ConstEvalInt(item->data_type.packed_dim_right, scope);
  for (auto* dim : item->unpacked_dims) {
    if (dim && dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto l = ConstEvalInt(dim->lhs, scope);
      auto rr = ConstEvalInt(dim->rhs, scope);
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
    ranges.emplace(item->name,
                   CollectPlaDeclRanges(item, pla_ascending_scope_));
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
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      e->args.size() >= 2 && e->args[0] && e->args[1] &&
      e->args[0]->kind == ExprKind::kIdentifier) {
    // §20.7: the dimension index is a constant expression, so fold it in the
    // module's parameter scope. This resolves a parameter, localparam, or
    // genvar-valued n the same way a literal one is resolved; a non-constant
    // (e.g. run-time-variable) index folds to nothing and is left alone.
    auto n_val = ConstEvalInt(e->args[1], scope);
    auto it = vars.find(e->args[0]->text);
    if (n_val && *n_val > 1 && it != vars.end()) {
      auto n = static_cast<uint64_t>(*n_val);
      const std::vector<Expr*>& dims = *it->second;
      if (n <= dims.size() && DimIsVariableSized(dims[n - 1])) {
        diag.Error(e->range.start,
                   std::format("array query function '{}' cannot query "
                               "variable-sized dimension {} of array '{}'",
                               e->callee, n, e->args[0]->text),
                   Subclause("20.7.1"));
      }
    }
  }
  CheckArrayQueryOnVarDimExpr(e->lhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->rhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->condition, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->true_expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->false_expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->base, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->index, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->index_end, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->repeat_count, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->with_expr, vars, scope, diag);
  for (auto* a : e->args) CheckArrayQueryOnVarDimExpr(a, vars, scope, diag);
  for (auto* el : e->elements)
    CheckArrayQueryOnVarDimExpr(el, vars, scope, diag);
}

void CheckArrayQueryOnVarDimStmt(const Stmt* s, const VarDimMap& vars,
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnVarDimExpr(s->condition, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->lhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->rhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->delay, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->var_init, vars, scope, diag);
  for (auto* sub : s->stmts)
    CheckArrayQueryOnVarDimStmt(sub, vars, scope, diag);
  for (auto* sub : s->fork_stmts)
    CheckArrayQueryOnVarDimStmt(sub, vars, scope, diag);
  CheckArrayQueryOnVarDimStmt(s->then_branch, vars, scope, diag);
  CheckArrayQueryOnVarDimStmt(s->else_branch, vars, scope, diag);
  CheckArrayQueryOnVarDimStmt(s->body, vars, scope, diag);
  CheckArrayQueryOnVarDimStmt(s->for_body, vars, scope, diag);
  for (auto* init : s->for_inits)
    CheckArrayQueryOnVarDimStmt(init, vars, scope, diag);
  for (auto& ci : s->case_items)
    CheckArrayQueryOnVarDimStmt(ci.body, vars, scope, diag);
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
  const ScopeMap& scope = array_query_dim_scope_;
  for (const auto* item : decl->items) {
    if (item->body) CheckArrayQueryOnVarDimStmt(item->body, vars, scope, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnVarDimStmt(s, vars, scope, diag_);
    CheckArrayQueryOnVarDimExpr(item->init_expr, vars, scope, diag_);
  }
}

}  // namespace delta
