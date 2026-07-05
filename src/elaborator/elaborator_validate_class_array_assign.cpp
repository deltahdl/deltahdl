#include <cstdint>
#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §7.4/§7.8 — the two array operands of a single assignment: the left-hand and
// right-hand tracked arrays (`l`/`r`) together with the identifier expressions
// that named them (`lhs`/`rhs`) and the source location of the assignment. The
// shape/element compatibility checks all act on this one assignment entity, so
// they take it as a unit rather than threading the five values separately.
struct ArrayAssignPair {
  const Elaborator::VarArrayInfo& l;
  const Elaborator::VarArrayInfo& r;
  const Expr* lhs;
  const Expr* rhs;
  SourceLoc loc;
};

// True when both tracked arrays are fixed-size, equally ranked, and have more
// than one unpacked dimension -- the precondition for a faster-varying
// dimension size comparison.
bool BothFixedMultiDim(const Elaborator::VarArrayInfo& l,
                       const Elaborator::VarArrayInfo& r) {
  return !l.is_dynamic && !r.is_dynamic && !l.is_assoc && !r.is_assoc &&
         l.dim_sizes.size() == r.dim_sizes.size() && l.dim_sizes.size() > 1;
}

// Emits the faster-varying dimension size-mismatch diagnostic for dimension
// `i` of the two tracked arrays.
void ReportFasterVaryingDimMismatchAt(const ArrayAssignPair& p, size_t i,
                                      DiagEngine& diag) {
  diag.Error(p.loc,
             std::format("faster-varying array dimension size mismatch in "
                         "assignment ('{}' dim {} is {}, '{}' dim {} is {})",
                         p.lhs->text, i, p.l.dim_sizes[i], p.rhs->text, i,
                         p.r.dim_sizes[i]));
}

// Reports the first faster-varying (non-leftmost) unpacked dimension whose
// size differs between the two fixed-size arrays. Returns true (with a
// diagnostic emitted) when a mismatch is found, mirroring the early return of
// the caller.
bool ReportFasterVaryingDimMismatch(const ArrayAssignPair& p,
                                    DiagEngine& diag) {
  if (!BothFixedMultiDim(p.l, p.r)) return false;
  for (size_t i = 1; i < p.l.dim_sizes.size(); ++i) {
    if (p.l.dim_sizes[i] != p.r.dim_sizes[i]) {
      ReportFasterVaryingDimMismatchAt(p, i, diag);
      return true;
    }
  }
  return false;
}

// §7.6 — the slowest-varying (leftmost) dimension of a dynamic array or queue
// may differ in kind and its size is not known until run time, but every
// faster-varying dimension shall still meet the §6.22.2 equivalence
// requirement, which for a fixed dimension means an identical declared size.
// The leftmost dynamic/queue dimension contributes no entry to `dim_sizes`, so
// when both arrays have a dynamic/queue leftmost dimension backed by a full
// complement of fixed faster dimensions, `dim_sizes` holds exactly those faster
// dimensions and comparing the two vectors element-wise enforces the rule for
// that declaration shape. The both-fixed shape is handled separately, and the
// leftmost dimension is intentionally left uncompared here.
bool ReportFasterVaryingDimMismatchVarOuter(const ArrayAssignPair& p,
                                            DiagEngine& diag) {
  const Elaborator::VarArrayInfo& l = p.l;
  const Elaborator::VarArrayInfo& r = p.r;
  bool l_var_outer = (l.is_dynamic || l.is_queue) && !l.is_assoc;
  bool r_var_outer = (r.is_dynamic || r.is_queue) && !r.is_assoc;
  if (!l_var_outer || !r_var_outer) return false;
  if (l.num_unpacked_dims != r.num_unpacked_dims) return false;
  if (l.num_unpacked_dims < 2) return false;
  if (l.dim_sizes.size() != l.num_unpacked_dims - 1) return false;
  if (r.dim_sizes.size() != r.num_unpacked_dims - 1) return false;
  for (size_t i = 0; i < l.dim_sizes.size(); ++i) {
    if (l.dim_sizes[i] != r.dim_sizes[i]) {
      diag.Error(p.loc, std::format(
                            "faster-varying array dimension size mismatch in "
                            "assignment ('{}' dim {} is {}, '{}' dim {} is {})",
                            p.lhs->text, i + 1, l.dim_sizes[i], p.rhs->text,
                            i + 1, r.dim_sizes[i]));
      return true;
    }
  }
  return false;
}

// Reports an associativity / associative-index-type mismatch between two
// tracked arrays. Returns true (with a diagnostic emitted) when found.
bool ReportAssocKindMismatch(const Elaborator::VarArrayInfo& l,
                             const Elaborator::VarArrayInfo& r, SourceLoc loc,
                             DiagEngine& diag) {
  if (l.is_assoc != r.is_assoc) {
    diag.Error(loc,
               "associative array cannot be assigned to or from a "
               "non-associative array");
    return true;
  }
  if (l.is_assoc && r.is_assoc && l.assoc_index_type != r.assoc_index_type) {
    diag.Error(loc, "associative array index type mismatch in assignment");
    return true;
  }
  return false;
}

// Reports a mismatch in the number of unpacked dimensions between two tracked
// arrays. Returns true (with a diagnostic emitted) when found.
bool ReportUnpackedDimCountMismatch(const ArrayAssignPair& p,
                                    DiagEngine& diag) {
  if (p.l.num_unpacked_dims != p.r.num_unpacked_dims) {
    diag.Error(p.loc,
               std::format("array assignment requires the same number of "
                           "unpacked dimensions ('{}' has {}, '{}' has {})",
                           p.lhs->text, p.l.num_unpacked_dims, p.rhs->text,
                           p.r.num_unpacked_dims));
    return true;
  }
  return false;
}

// Reports an element-type mismatch between two tracked arrays. Returns true
// (with a diagnostic emitted) when found.
bool ReportElementTypeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (!ElementTypesEquivalent({p.l.elem_type, p.l.elem_width,
                               p.l.elem_is_signed, p.l.elem_is_4state},
                              {p.r.elem_type, p.r.elem_width,
                               p.r.elem_is_signed, p.r.elem_is_4state})) {
    diag.Error(p.loc, std::format("array element type mismatch in assignment "
                                  "('{}' vs '{}')",
                                  p.lhs->text, p.rhs->text));
    return true;
  }
  return false;
}

// Reports a fixed-size element-count mismatch between two tracked arrays.
// Returns true (with a diagnostic emitted) when found.
bool ReportFixedSizeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (p.l.unpacked_size > 0 && !p.l.is_dynamic && p.r.unpacked_size > 0 &&
      !p.r.is_dynamic && p.l.unpacked_size != p.r.unpacked_size) {
    diag.Error(p.loc,
               std::format("array size mismatch: '{}' has {} elements but "
                           "'{}' has {}",
                           p.lhs->text, p.l.unpacked_size, p.rhs->text,
                           p.r.unpacked_size));
    return true;
  }
  return false;
}

// Validates the kind/shape compatibility of two tracked arrays in an
// assignment (associativity, index type, dimension count, element type, and
// fixed-size element count). Returns true (with a diagnostic emitted) when the
// first incompatibility is found, mirroring the caller's early returns.
bool ReportArrayShapeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (ReportAssocKindMismatch(p.l, p.r, p.loc, diag)) return true;
  if (ReportUnpackedDimCountMismatch(p, diag)) return true;
  if (ReportElementTypeMismatch(p, diag)) return true;
  if (ReportFixedSizeMismatch(p, diag)) return true;
  return false;
}

}  // namespace

void Elaborator::CheckArrayAssignExprs(const Expr* lhs, const Expr* rhs,
                                       SourceLoc loc) {
  if (!lhs || !rhs) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  if (rhs->kind != ExprKind::kIdentifier) return;
  auto lhs_it = var_array_info_.find(lhs->text);
  auto rhs_it = var_array_info_.find(rhs->text);
  if (lhs_it == var_array_info_.end() || rhs_it == var_array_info_.end()) {
    if (lhs_it != var_array_info_.end() &&
        packed_array_vars_.count(rhs->text)) {
      diag_.Error(loc,
                  std::format("packed array '{}' cannot be directly assigned "
                              "to unpacked array '{}' without an explicit cast",
                              rhs->text, lhs->text));
    }
    return;
  }
  const ArrayAssignPair kPair{lhs_it->second, rhs_it->second, lhs, rhs, loc};

  if (ReportArrayShapeMismatch(kPair, diag_)) return;
  if (ReportFasterVaryingDimMismatch(kPair, diag_)) return;
  if (ReportFasterVaryingDimMismatchVarOuter(kPair, diag_)) return;
}

void Elaborator::ValidateOneArrayAssignment(const ModuleItem* item) {
  if (!item->assign_lhs || !item->assign_rhs) return;
  CheckArrayAssignExprs(item->assign_lhs, item->assign_rhs, item->loc);
}

void Elaborator::WalkStmtsForArrayAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayAssignExprs(s->lhs, s->rhs, s->range.start);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayAssign(sub);
  WalkStmtsForArrayAssign(s->then_branch);
  WalkStmtsForArrayAssign(s->else_branch);
  WalkStmtsForArrayAssign(s->body);
  WalkStmtsForArrayAssign(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayAssign(ci.body);
}

void Elaborator::ValidateArrayAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ValidateOneArrayAssignment(item);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForArrayAssign(item->body);
    }
  }
}

static Elaborator::VarArrayInfo FormalArrayInfo(
    const FunctionArg& arg,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs) {
  Elaborator::VarArrayInfo info;
  info.elem_type = arg.data_type.kind;
  info.elem_width = EvalTypeWidth(arg.data_type, typedefs);
  info.elem_is_signed = arg.data_type.is_signed;
  info.elem_is_4state = Is4stateType(arg.data_type, typedefs);
  if (arg.unpacked_dims.empty()) return info;
  auto* dim = arg.unpacked_dims[0];
  if (!dim) {
    info.is_dynamic = true;
    return info;
  }
  if (dim->kind == ExprKind::kIdentifier) {
    auto t = dim->text;
    if (t == "$") return info;
    if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
        t == "shortint" || t == "longint" || t == "*") {
      info.is_assoc = true;
      info.assoc_index_type = t;
      return info;
    }
    if (class_names.count(t) > 0) {
      info.is_assoc = true;
      info.assoc_index_type = t;
      return info;
    }
  }

  info.unpacked_size = 1;
  return info;
}

// Resolves the index into `expr->args` that binds to the formal at position
// `formal_index` (named `formal_name`), handling pure-positional, mixed, and
// named-argument call forms. Returns -1 when no actual binds to the formal.
static int ResolveActualArgIndex(const Expr* expr, size_t formal_index,
                                 std::string_view formal_name,
                                 size_t positional_count) {
  if (expr->arg_names.empty()) {
    return (formal_index < expr->args.size()) ? static_cast<int>(formal_index)
                                              : -1;
  }
  if (formal_index < positional_count) return static_cast<int>(formal_index);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == formal_name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

// Reports the associative-array compatibility errors for binding a single
// identifier actual to an array-typed formal (associativity, index type, and
// element type). At most one diagnostic is emitted per actual.
static void CheckArrayArgCompat(const Expr* actual,
                                const Elaborator::VarArrayInfo& actual_info,
                                const Elaborator::VarArrayInfo& formal_info,
                                DiagEngine& diag) {
  if (actual_info.is_assoc != formal_info.is_assoc) {
    diag.Error(actual->range.start,
               "associative array cannot be passed to or from a "
               "non-associative array parameter");
    return;
  }
  if (actual_info.is_assoc && formal_info.is_assoc &&
      actual_info.assoc_index_type != formal_info.assoc_index_type) {
    diag.Error(actual->range.start,
               "associative array index type mismatch in argument");
    return;
  }
  // The value type carried by an associative actual must be equivalent to the
  // value type of the associative formal it binds to.
  if (actual_info.is_assoc && formal_info.is_assoc &&
      !ElementTypesEquivalent(
          {actual_info.elem_type, actual_info.elem_width,
           actual_info.elem_is_signed, actual_info.elem_is_4state},
          {formal_info.elem_type, formal_info.elem_width,
           formal_info.elem_is_signed, formal_info.elem_is_4state})) {
    diag.Error(actual->range.start,
               "associative array element type mismatch in argument");
    return;
  }
}

// §13.5 — the immutable lookup environment for resolving and type-checking a
// subroutine call's array arguments: the visible function/task declarations,
// the tracked-array map, the class-name set, the typedef map, and the
// diagnostic sink. It is threaded through the argument-type tree walk so each
// recursive visit is a single short call rather than a multi-argument forward.
struct ArrayArgTypeCtx {
  const std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const std::unordered_set<std::string_view>& class_names;
  const TypedefMap& typedefs;
  DiagEngine& diag;
};

// Checks the single formal at position `formal_index` of `func` against the
// actual that binds to it in the call `expr`, reporting any associative-array
// incompatibility. Array-typed formals with no bound identifier actual are
// silently skipped, mirroring the caller's per-formal continues.
static void CheckOneArrayFormalArg(const Expr* expr, const ModuleItem* func,
                                   size_t formal_index, size_t positional_count,
                                   const ArrayArgTypeCtx& ctx) {
  const auto& formal = func->func_args[formal_index];
  if (formal.unpacked_dims.empty()) return;
  auto formal_info = FormalArrayInfo(formal, ctx.class_names, ctx.typedefs);
  int ai =
      ResolveActualArgIndex(expr, formal_index, formal.name, positional_count);
  if (ai < 0) return;
  auto* actual = expr->args[static_cast<size_t>(ai)];
  if (!actual || actual->kind != ExprKind::kIdentifier) return;
  auto ait = ctx.var_array_info.find(actual->text);
  if (ait == ctx.var_array_info.end()) return;
  CheckArrayArgCompat(actual, ait->second, formal_info, ctx.diag);
}

static void CheckArrayArgTypes(const Expr* expr, const ArrayArgTypeCtx& ctx) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = ctx.func_decls.find(expr->callee);
  if (it == ctx.func_decls.end()) return;
  const auto* func = it->second;
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    CheckOneArrayFormalArg(expr, func, i, positional_count, ctx);
  }
}

static void WalkExprForArrayArgTypes(const Expr* expr,
                                     const ArrayArgTypeCtx& ctx) {
  if (!expr) return;
  CheckArrayArgTypes(expr, ctx);
  WalkExprForArrayArgTypes(expr->lhs, ctx);
  WalkExprForArrayArgTypes(expr->rhs, ctx);
  WalkExprForArrayArgTypes(expr->condition, ctx);
  WalkExprForArrayArgTypes(expr->true_expr, ctx);
  WalkExprForArrayArgTypes(expr->false_expr, ctx);
  for (auto* a : expr->args) WalkExprForArrayArgTypes(a, ctx);
  for (auto* e : expr->elements) WalkExprForArrayArgTypes(e, ctx);
}

static void WalkStmtForArrayArgTypes(const Stmt* s,
                                     const ArrayArgTypeCtx& ctx) {
  if (!s) return;
  WalkExprForArrayArgTypes(s->expr, ctx);
  WalkExprForArrayArgTypes(s->lhs, ctx);
  WalkExprForArrayArgTypes(s->rhs, ctx);
  WalkExprForArrayArgTypes(s->condition, ctx);
  for (auto* sub : s->stmts) WalkStmtForArrayArgTypes(sub, ctx);
  WalkStmtForArrayArgTypes(s->then_branch, ctx);
  WalkStmtForArrayArgTypes(s->else_branch, ctx);
  WalkStmtForArrayArgTypes(s->body, ctx);
  for (auto* fi : s->for_inits) WalkStmtForArrayArgTypes(fi, ctx);
  WalkStmtForArrayArgTypes(s->for_body, ctx);
  for (auto* fs : s->for_steps) WalkStmtForArrayArgTypes(fs, ctx);
  WalkExprForArrayArgTypes(s->for_cond, ctx);
  for (auto& ci : s->case_items) WalkStmtForArrayArgTypes(ci.body, ctx);
}

void Elaborator::ValidateArrayArgTypes(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  const ArrayArgTypeCtx kCtx{all_decls, var_array_info_, class_names_,
                             typedefs_, diag_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      WalkStmtForArrayArgTypes(item->body, kCtx);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        WalkStmtForArrayArgTypes(s, kCtx);
      }
    }
  }
}

bool IsSliceSelect(const Expr* e) {
  if (!e || e->kind != ExprKind::kSelect) return false;
  return e->is_part_select_plus || e->is_part_select_minus || e->index_end;
}

static void CheckAssocSliceExpr(
    const Expr* e, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!e) return;
  if (IsSliceSelect(e) && e->base && e->base->kind == ExprKind::kIdentifier) {
    if (assoc_names.count(e->base->text)) {
      diag.Error(e->range.start,
                 "slice is not allowed on an associative array");
    }
  }
  CheckAssocSliceExpr(e->lhs, assoc_names, diag);
  CheckAssocSliceExpr(e->rhs, assoc_names, diag);
  CheckAssocSliceExpr(e->base, assoc_names, diag);
  CheckAssocSliceExpr(e->index, assoc_names, diag);
  CheckAssocSliceExpr(e->index_end, assoc_names, diag);
  CheckAssocSliceExpr(e->condition, assoc_names, diag);
  CheckAssocSliceExpr(e->true_expr, assoc_names, diag);
  CheckAssocSliceExpr(e->false_expr, assoc_names, diag);
  for (const auto* elem : e->elements) {
    CheckAssocSliceExpr(elem, assoc_names, diag);
  }
}

static void WalkStmtsForAssocSlice(
    const Stmt* s, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckAssocSliceExpr(s->lhs, assoc_names, diag);
  CheckAssocSliceExpr(s->rhs, assoc_names, diag);
  CheckAssocSliceExpr(s->expr, assoc_names, diag);
  CheckAssocSliceExpr(s->condition, assoc_names, diag);
  for (auto* sub : s->stmts) WalkStmtsForAssocSlice(sub, assoc_names, diag);
  WalkStmtsForAssocSlice(s->then_branch, assoc_names, diag);
  WalkStmtsForAssocSlice(s->else_branch, assoc_names, diag);
  WalkStmtsForAssocSlice(s->body, assoc_names, diag);
  WalkStmtsForAssocSlice(s->for_body, assoc_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForAssocSlice(ci.body, assoc_names, diag);
}

void Elaborator::ValidateAssocArraySlices(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> assoc_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc) assoc_names.insert(name);
  }
  if (assoc_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssocSliceExpr(item->assign_lhs, assoc_names, diag_);
      CheckAssocSliceExpr(item->assign_rhs, assoc_names, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForAssocSlice(item->body, assoc_names, diag_);
    }
  }
}

static bool IsTraversalMethod(std::string_view name) {
  return name == "first" || name == "last" || name == "next" || name == "prev";
}

// §7.8.1 — array manipulation methods (§7.12) that yield an index value or an
// array of index values. A wildcard-indexed associative array may not be used
// with these, since its keys have no stable index domain to return. This
// includes unique_index, which returns an array of the qualifying indices.
static bool IsIndexReturningMethod(std::string_view name) {
  return name == "find_index" || name == "find_first_index" ||
         name == "find_last_index" || name == "unique_index";
}

// §7.8.1 — true when `idx` is a nonintegral index expression for a wildcard
// associative array: a real literal, or an identifier of a real/shortreal/
// realtime variable. (A string literal is not nonintegral here; it is cast to
// an equivalent-width bit vector.)
bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types) {
  if (!idx) return false;
  if (idx->kind == ExprKind::kRealLiteral) return true;
  if (idx->kind == ExprKind::kIdentifier) {
    auto it = var_types.find(idx->text);
    return it != var_types.end() && IsRealType(it->second);
  }
  return false;
}

static void CheckWildcardTraversalExpr(
    const Expr* e, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier && IsTraversalMethod(e->callee) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->callee, e->base->text));
  }
  // §7.8.1 — an array-locator method (e.g. `aa.find_index with (...)`) parses
  // as a member access whose receiver is the array and whose member is the
  // method name. Reject the index-returning locators on a wildcard array.
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs &&
      IsIndexReturningMethod(e->rhs->text) &&
      wildcard_names.count(e->lhs->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->rhs->text, e->lhs->text));
  }
  // §7.8.1 — a wildcard index must be integral; a real (nonintegral) value used
  // to index the array is illegal.
  if (e->kind == ExprKind::kSelect && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      IsNonintegralIndex(e->index, var_types) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->index->range.start,
               std::format("nonintegral index is not allowed on wildcard "
                           "associative array '{}'",
                           e->base->text));
  }
  CheckWildcardTraversalExpr(e->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->base, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index_end, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->condition, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->true_expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->false_expr, wildcard_names, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckWildcardTraversalExpr(elem, wildcard_names, var_types, diag);
  }
}

static void WalkStmtsForWildcardTraversal(
    const Stmt* s, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  // §7.8.1 — a wildcard-indexed associative array may not drive a foreach loop.
  if (s->kind == StmtKind::kForeach && s->expr &&
      (s->expr->kind == ExprKind::kIdentifier ||
       s->expr->kind == ExprKind::kMemberAccess) &&
      wildcard_names.count(s->expr->text)) {
    diag.Error(s->range.start,
               std::format("wildcard associative array '{}' may not be used in "
                           "a foreach loop",
                           s->expr->text));
  }
  CheckWildcardTraversalExpr(s->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->condition, wildcard_names, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForWildcardTraversal(sub, wildcard_names, var_types, diag);
  WalkStmtsForWildcardTraversal(s->then_branch, wildcard_names, var_types,
                                diag);
  WalkStmtsForWildcardTraversal(s->else_branch, wildcard_names, var_types,
                                diag);
  WalkStmtsForWildcardTraversal(s->body, wildcard_names, var_types, diag);
  WalkStmtsForWildcardTraversal(s->for_body, wildcard_names, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForWildcardTraversal(ci.body, wildcard_names, var_types, diag);
}

void Elaborator::ValidateAssocWildcardTraversal(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> wildcard_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc && info.assoc_index_type == "*")
      wildcard_names.insert(name);
  }
  if (wildcard_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckWildcardTraversalExpr(item->assign_lhs, wildcard_names, var_types_,
                                 diag_);
      CheckWildcardTraversalExpr(item->assign_rhs, wildcard_names, var_types_,
                                 diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForWildcardTraversal(item->body, wildcard_names, var_types_,
                                    diag_);
    }
  }
}

// Section 7.9.8 -- the argument passed to one of the four associative-array
// traversal methods (first/last/next/prev) shall be assignment compatible with
// the array's index type. A string-indexed array therefore requires a string
// argument and an integral-indexed array requires an integral argument; the two
// categories are not assignment compatible with each other. A narrower integral
// argument is still assignment compatible -- the resulting truncation is
// resolved at run time and is not flagged during elaboration.
enum class AssocKeyCategory : std::uint8_t {
  kOther,
  kStringKey,
  kIntegralKey,
  kWildcard
};

static AssocKeyCategory ClassifyAssocKey(std::string_view index_type,
                                         const TypedefMap& typedefs) {
  if (index_type == "string") return AssocKeyCategory::kStringKey;
  auto builtin_integral = [](std::string_view t) {
    return t == "bit" || t == "logic" || t == "reg" || t == "byte" ||
           t == "shortint" || t == "int" || t == "longint" || t == "integer" ||
           t == "time";
  };
  if (builtin_integral(index_type)) return AssocKeyCategory::kIntegralKey;
  auto it = typedefs.find(index_type);
  if (it != typedefs.end() && IsIntegralType(it->second.kind))
    return AssocKeyCategory::kIntegralKey;
  return AssocKeyCategory::kOther;
}

static bool TraversalArgIsString(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && it->second == DataTypeKind::kString;
}

static bool TraversalArgIsIntegral(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && IsIntegralType(it->second);
}

// Reports a traversal-method call (`arr.first(x)` etc.) whose argument type is
// not assignment compatible with the associative array's index category. Only
// the call node itself is examined; child expressions are walked by the caller.
static void CheckTraversalCallSite(
    const Expr* e,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  // `arr.first(x)` parses as a kCall whose lhs is the member access `arr.first`
  // and whose args hold the traversal argument.
  if (e->kind != ExprKind::kCall || !e->lhs ||
      e->lhs->kind != ExprKind::kMemberAccess || e->args.empty()) {
    return;
  }
  const Expr* access = e->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier ||
      !access->rhs || access->rhs->kind != ExprKind::kIdentifier ||
      !IsTraversalMethod(access->rhs->text)) {
    return;
  }
  auto array_name = access->lhs->text;
  auto method = access->rhs->text;
  auto it = assoc_keys.find(array_name);
  if (it == assoc_keys.end()) return;
  // §7.9.4-7.9.7: first/last/next/prev shall not be used on a wildcard-indexed
  // associative array.
  if (it->second == AssocKeyCategory::kWildcard) {
    diag.Error(e->range.start,
               std::format("traversal method '{}' shall not be used on the "
                           "wildcard-indexed associative array '{}'",
                           method, array_name));
    return;
  }
  const Expr* arg = e->args[0];
  bool wrong = (it->second == AssocKeyCategory::kStringKey &&
                TraversalArgIsIntegral(arg, var_types)) ||
               (it->second == AssocKeyCategory::kIntegralKey &&
                TraversalArgIsString(arg, var_types));
  if (wrong) {
    diag.Error(arg ? arg->range.start : e->range.start,
               std::format("traversal method '{}' argument is not "
                           "assignment compatible with the index type of "
                           "associative array '{}'",
                           method, array_name));
  }
}

static void CheckTraversalArgTypeExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  CheckTraversalCallSite(e, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->base, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index_end, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->condition, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->true_expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->false_expr, assoc_keys, var_types, diag);
  for (const auto* a : e->args)
    CheckTraversalArgTypeExpr(a, assoc_keys, var_types, diag);
  for (const auto* el : e->elements)
    CheckTraversalArgTypeExpr(el, assoc_keys, var_types, diag);
}

static void WalkStmtsForTraversalArgType(
    const Stmt* s,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckTraversalArgTypeExpr(s->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->condition, assoc_keys, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForTraversalArgType(sub, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->then_branch, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->else_branch, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->body, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->for_body, assoc_keys, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForTraversalArgType(ci.body, assoc_keys, var_types, diag);
}

void Elaborator::ValidateAssocTraversalArgType(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, AssocKeyCategory> assoc_keys;
  for (const auto& [name, info] : var_array_info_) {
    if (!info.is_assoc) continue;
    if (info.assoc_index_type == "*") {
      assoc_keys[name] = AssocKeyCategory::kWildcard;
      continue;
    }
    auto cat = ClassifyAssocKey(info.assoc_index_type, typedefs_);
    if (cat != AssocKeyCategory::kOther) assoc_keys[name] = cat;
  }
  if (assoc_keys.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTraversalArgTypeExpr(item->assign_lhs, assoc_keys, var_types_,
                                diag_);
      CheckTraversalArgTypeExpr(item->assign_rhs, assoc_keys, var_types_,
                                diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForTraversalArgType(item->body, assoc_keys, var_types_, diag_);
  }
}

// §7.12.2: the array ordering methods. reverse() and shuffle() take no with
// clause, whereas sort() and rsort() accept an optional one.
static bool IsArrayOrderingMethod(std::string_view name) {
  return name == "sort" || name == "rsort" || name == "reverse" ||
         name == "shuffle";
}

static bool OrderingMethodRejectsWith(std::string_view name) {
  return name == "reverse" || name == "shuffle";
}

// Recognize an array-method invocation, in either the call form `arr.m()` or
// the property form `arr.m`. On success, `base` is the receiver expression,
// `method` is the method name, and `has_with` records whether a with clause
// was attached (the parser hangs it on the outermost expression in both
// forms).
struct OrderingMethodSite {
  const Expr* base = nullptr;
  std::string_view method;
  bool has_with = false;
};

static bool MatchOrderingMethodSite(const Expr* e, OrderingMethodSite& out) {
  if (!e) return false;
  const Expr* access = nullptr;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    access = e->lhs;
  } else if (e->kind == ExprKind::kMemberAccess) {
    access = e;
  } else {
    return false;
  }
  if (!access->lhs || !access->rhs ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!IsArrayOrderingMethod(access->rhs->text)) return false;
  out.base = access->lhs;
  out.method = access->rhs->text;
  out.has_with = e->with_expr != nullptr;
  return true;
}

// §7.12.2: ordering methods reorder any fixed or dynamically sized unpacked
// array but are not defined on associative arrays, and reverse()/shuffle()
// reject a with clause. Each is reported as a compile-time error. The
// receiver is only checked against the array tracking map when it is a plain
// identifier, which is enough to recognize a declared associative array.
static void CheckArrayOrderingExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (!e) return;
  OrderingMethodSite site;
  if (MatchOrderingMethodSite(e, site) && site.base &&
      site.base->kind == ExprKind::kIdentifier) {
    auto it = var_array_info.find(site.base->text);
    if (it != var_array_info.end()) {
      if (it->second.is_assoc) {
        diag.Error(e->range.start,
                   std::format("array ordering method '{}' cannot be applied "
                               "to associative array '{}'",
                               site.method, site.base->text));
      } else if (site.has_with && OrderingMethodRejectsWith(site.method)) {
        diag.Error(e->range.start,
                   std::format("array ordering method '{}' does not accept a "
                               "'with' clause",
                               site.method));
      }
    }
  }
  CheckArrayOrderingExpr(e->lhs, var_array_info, diag);
  CheckArrayOrderingExpr(e->rhs, var_array_info, diag);
  CheckArrayOrderingExpr(e->base, var_array_info, diag);
  CheckArrayOrderingExpr(e->index, var_array_info, diag);
  CheckArrayOrderingExpr(e->condition, var_array_info, diag);
  CheckArrayOrderingExpr(e->true_expr, var_array_info, diag);
  CheckArrayOrderingExpr(e->false_expr, var_array_info, diag);
  for (const auto* a : e->args) CheckArrayOrderingExpr(a, var_array_info, diag);
  for (const auto* elem : e->elements)
    CheckArrayOrderingExpr(elem, var_array_info, diag);
}

static void WalkStmtsForArrayOrdering(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (!s) return;
  CheckArrayOrderingExpr(s->expr, var_array_info, diag);
  CheckArrayOrderingExpr(s->lhs, var_array_info, diag);
  CheckArrayOrderingExpr(s->rhs, var_array_info, diag);
  CheckArrayOrderingExpr(s->condition, var_array_info, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForArrayOrdering(sub, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->then_branch, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->else_branch, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->body, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->for_body, var_array_info, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForArrayOrdering(ci.body, var_array_info, diag);
}

void Elaborator::ValidateArrayOrderingMethods(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckArrayOrderingExpr(item->assign_lhs, var_array_info_, diag_);
      CheckArrayOrderingExpr(item->assign_rhs, var_array_info_, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForArrayOrdering(item->body, var_array_info_, diag_);
    }
  }
}

}  // namespace delta
