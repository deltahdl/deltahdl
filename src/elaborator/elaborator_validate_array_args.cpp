#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_array_shape.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// §13.5 — the immutable lookup environment for resolving and type-checking a
// subroutine call's array arguments: the visible function/task declarations,
// the tracked-array map, the class-name set, the typedef map, the names of
// typedefs of unpacked aggregates, the module's parameter scope for folding a
// formal's bounds, and the diagnostic sink. It is threaded through the
// argument-type tree walk so each recursive visit is a single short call rather
// than a multi-argument forward.
struct ArrayArgTypeCtx {
  const std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const std::unordered_set<std::string_view>& class_names;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  const ScopeMap& scope;
  DiagEngine& diag;
};

// §7.7: the formal side of an array argument binding, described as a tracked
// array is so the two can be compared. The element type is resolved through
// typedef names as a declared variable's is, so that `word_t a[3]` under
// `typedef int word_t;` compares as int.
static Elaborator::VarArrayInfo FormalArrayInfo(const FunctionArg& arg,
                                                const ArrayArgTypeCtx& ctx) {
  Elaborator::VarArrayInfo info;
  info.elem_type = ElementKindThroughTypedefs(arg.data_type, ctx.typedefs);
  info.elem_width = EvalTypeWidth(arg.data_type, ctx.typedefs);
  info.elem_is_signed = IsSignedType(arg.data_type, ctx.typedefs);
  info.elem_is_4state = Is4stateType(arg.data_type, ctx.typedefs);
  info.num_unpacked_dims = static_cast<uint32_t>(arg.unpacked_dims.size());
  info.unpacked_shape = UnpackedShapeOf(arg.data_type, arg.unpacked_dims,
                                        ctx.aggregate_typedefs, ctx.scope);
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
    if (ctx.class_names.count(t) > 0) {
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
// element type). At most one diagnostic is emitted per actual, and true is
// returned when it was.
static bool CheckArrayArgCompat(const Expr* actual,
                                const Elaborator::VarArrayInfo& actual_info,
                                const Elaborator::VarArrayInfo& formal_info,
                                DiagEngine& diag) {
  if (actual_info.is_assoc != formal_info.is_assoc) {
    diag.Error(actual->range.start,
               "associative array cannot be passed to or from a "
               "non-associative array parameter",
               Subclause("7.9.10"));
    return true;
  }
  if (actual_info.is_assoc && formal_info.is_assoc &&
      actual_info.assoc_index_type != formal_info.assoc_index_type) {
    diag.Error(actual->range.start,
               "associative array index type mismatch in argument",
               Subclause("7.9.10"));
    return true;
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
               "associative array element type mismatch in argument",
               Subclause("7.9.10"));
    return true;
  }
  return false;
}

// §7.7 with §7.6: a non-associative array actual is associated with its formal
// only when the two have the same number of unpacked dimensions and, in every
// dimension where both have a size of their own, the same size; an unsized
// dimension on either side matches any size, its size checked at run time.
// Returns true when a diagnostic was emitted.
static bool ReportArrayArgShapeMismatch(
    const Expr* actual, std::string_view formal_name,
    const std::vector<std::optional<uint32_t>>& actual_shape,
    const std::vector<std::optional<uint32_t>>& formal_shape,
    DiagEngine& diag) {
  if (actual_shape.size() != formal_shape.size()) {
    diag.Error(actual->range.start,
               std::format("array argument '{}' has {} unpacked dimension(s) "
                           "but formal '{}' has {}",
                           actual->text, actual_shape.size(), formal_name,
                           formal_shape.size()),
               Subclause("7.7"));
    return true;
  }
  for (size_t i = 0; i < actual_shape.size(); ++i) {
    if (!actual_shape[i] || !formal_shape[i]) continue;
    if (*actual_shape[i] == *formal_shape[i]) continue;
    diag.Error(actual->range.start,
               std::format("unpacked dimension {} of array argument '{}' has "
                           "size {} but formal '{}' has size {}",
                           i + 1, actual->text, *actual_shape[i], formal_name,
                           *formal_shape[i]),
               Subclause("7.7"));
    return true;
  }
  return false;
}

// §7.7 with §7.6 and §6.22.2: the elements of a non-associative array actual
// shall be of a type equivalent to the formal's elements. A type left named --
// a class, an enumeration, a name with no typedef -- is not judged here, its
// width and state not being what the comparison needs.
static void ReportArrayArgElementMismatch(
    const Expr* actual, std::string_view formal_name,
    const Elaborator::VarArrayInfo& actual_info,
    const Elaborator::VarArrayInfo& formal_info, DiagEngine& diag) {
  if (actual_info.elem_type == DataTypeKind::kNamed ||
      formal_info.elem_type == DataTypeKind::kNamed) {
    return;
  }
  if (ElementTypesEquivalent(
          {actual_info.elem_type, actual_info.elem_width,
           actual_info.elem_is_signed, actual_info.elem_is_4state},
          {formal_info.elem_type, formal_info.elem_width,
           formal_info.elem_is_signed, formal_info.elem_is_4state})) {
    return;
  }
  diag.Error(actual->range.start,
             std::format("element type of array argument '{}' is not "
                         "equivalent to that of formal '{}'",
                         actual->text, formal_name),
             Subclause("7.7"));
}

// Checks the single formal at position `formal_index` of `func` against the
// actual that binds to it in the call `expr`, reporting any associative-array
// incompatibility and, for a non-associative formal, any §7.7 shape or element
// type incompatibility. Array-typed formals with no bound identifier actual are
// silently skipped, mirroring the caller's per-formal continues.
static void CheckOneArrayFormalArg(const Expr* expr, const ModuleItem* func,
                                   size_t formal_index, size_t positional_count,
                                   const ArrayArgTypeCtx& ctx) {
  const auto& formal = func->func_args[formal_index];
  if (formal.unpacked_dims.empty()) return;
  auto formal_info = FormalArrayInfo(formal, ctx);
  int ai =
      ResolveActualArgIndex(expr, formal_index, formal.name, positional_count);
  if (ai < 0) return;
  auto* actual = expr->args[static_cast<size_t>(ai)];
  if (!actual || actual->kind != ExprKind::kIdentifier) return;
  auto ait = ctx.var_array_info.find(actual->text);
  if (ait == ctx.var_array_info.end()) return;
  const auto& actual_info = ait->second;
  if (CheckArrayArgCompat(actual, actual_info, formal_info, ctx.diag)) return;
  // The shape of an associative array is its index type, compared above.
  if (formal_info.is_assoc) return;
  if (actual_info.unpacked_shape.empty() ||
      formal_info.unpacked_shape.empty()) {
    return;
  }
  if (ReportArrayArgShapeMismatch(actual, formal.name,
                                  actual_info.unpacked_shape,
                                  formal_info.unpacked_shape, ctx.diag)) {
    return;
  }
  ReportArrayArgElementMismatch(actual, formal.name, actual_info, formal_info,
                                ctx.diag);
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

// §7.9.10 puts no condition on where the call whose argument it governs is
// written: it says an associative array can be passed only to an associative
// formal of a compatible type and with the same index type, and says nothing
// about the statement the call stands in. §13.5 makes a task or void function
// call a statement of a procedural block, and A.6.9's
// subroutine_call_statement is a statement, so such a call may appear in every
// position a statement holds a statement in and the check is owed at each of
// them.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions,
// once for the whole elaborator, which is why the list is not written out
// again here. It hands the visitor the field itself, so a walker that only
// reads the tree takes a `Stmt* const&`.
//
// Stmt::fork_stmts is descended into deliberately. A.6.3's par_block admits a
// statement_or_null in each arm, and neither §7.9.10 nor §13.5 makes argument
// compatibility depend on the process the call runs in, so a call in a fork
// arm binds its actuals to the same formals as one written beside the fork.
// That is what separates this rule from §13.4.4, which asks what a function
// body may schedule and so turns on whether the fork is there at all.
static void WalkStmtForArrayArgTypes(const Stmt* s,
                                     const ArrayArgTypeCtx& ctx) {
  if (!s) return;
  WalkExprForArrayArgTypes(s->expr, ctx);
  WalkExprForArrayArgTypes(s->lhs, ctx);
  WalkExprForArrayArgTypes(s->rhs, ctx);
  WalkExprForArrayArgTypes(s->condition, ctx);
  WalkExprForArrayArgTypes(s->for_cond, ctx);
  ForEachChildStmt(
      s, [&ctx](Stmt* const& sub) { WalkStmtForArrayArgTypes(sub, ctx); });
}

void Elaborator::ValidateArrayArgTypes(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  const ArrayArgTypeCtx kCtx{
      all_decls, var_array_info_,          class_names_,
      typedefs_, aggregate_typedef_names_, array_arg_dim_scope_,
      diag_};
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
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

}  // namespace delta
