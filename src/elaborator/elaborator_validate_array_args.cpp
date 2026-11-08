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

static Elaborator::VarArrayInfo FormalArrayInfo(const FunctionArg& arg,
                                                const ArrayArgTypeCtx& ctx) {
  Elaborator::VarArrayInfo info;
  info.elem_type = ElementKindThroughTypedefs(arg.data_type, ctx.typedefs);
  info.elem_type_name = ElementTypeIdentity(arg.data_type, ctx.typedefs);
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

int ResolveActualArgIndex(const Expr* expr, size_t formal_index,
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
  if (actual_info.is_assoc && formal_info.is_assoc &&
      !ElementTypesEquivalent(
          {actual_info.elem_type, actual_info.elem_width,
           actual_info.elem_is_signed, actual_info.elem_is_4state,
           actual_info.elem_type_name},
          {formal_info.elem_type, formal_info.elem_width,
           formal_info.elem_is_signed, formal_info.elem_is_4state,
           formal_info.elem_type_name})) {
    diag.Error(actual->range.start,
               "associative array element type mismatch in argument",
               Subclause("7.9.10"));
    return true;
  }
  return false;
}

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
    const std::optional<uint32_t> kActualSize = actual_shape[i];
    const std::optional<uint32_t> kFormalSize = formal_shape[i];
    if (!kActualSize || !kFormalSize) continue;
    if (*kActualSize == *kFormalSize) continue;
    diag.Error(actual->range.start,
               std::format("unpacked dimension {} of array argument '{}' has "
                           "size {} but formal '{}' has size {}",
                           i + 1, actual->text, *kActualSize, formal_name,
                           *kFormalSize),
               Subclause("7.7"));
    return true;
  }
  return false;
}

static void ReportArrayArgElementMismatch(
    const Expr* actual, std::string_view formal_name,
    const Elaborator::VarArrayInfo& actual_info,
    const Elaborator::VarArrayInfo& formal_info, DiagEngine& diag) {
  if (ElementTypesEquivalent(
          {actual_info.elem_type, actual_info.elem_width,
           actual_info.elem_is_signed, actual_info.elem_is_4state,
           actual_info.elem_type_name},
          {formal_info.elem_type, formal_info.elem_width,
           formal_info.elem_is_signed, formal_info.elem_is_4state,
           formal_info.elem_type_name})) {
    return;
  }
  diag.Error(actual->range.start,
             std::format("element type of array argument '{}' is not "
                         "equivalent to that of formal '{}'",
                         actual->text, formal_name),
             Subclause("7.7"));
}

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
