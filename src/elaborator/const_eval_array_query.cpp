#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct QueryDims {
  std::vector<RtlirUnpackedDim> dims;
  size_t unpacked = 0;
  bool has_packed = true;
};

using RangeExprs = std::vector<std::pair<const Expr*, const Expr*>>;

std::optional<std::vector<RtlirUnpackedDim>> FoldRanges(
    const RangeExprs& ranges, const ScopeMap& scope) {
  std::vector<RtlirUnpackedDim> dims;
  for (const auto& [left, right] : ranges) {
    auto lv = ConstEvalInt(left, scope);
    auto rv = ConstEvalInt(right, scope);
    if (!lv || !rv) return std::nullopt;
    dims.push_back(RtlirUnpackedDim{*lv, *rv});
  }
  return dims;
}

std::optional<RtlirUnpackedDim> KeywordDim(std::string_view kw) {
  if (kw == "byte") return RtlirUnpackedDim{7, 0};
  if (kw == "shortint") return RtlirUnpackedDim{15, 0};
  if (kw == "int" || kw == "integer") return RtlirUnpackedDim{31, 0};
  if (kw == "longint" || kw == "time") return RtlirUnpackedDim{63, 0};
  return std::nullopt;
}

bool IsIntegralKind(DataTypeKind kind) {
  static constexpr DataTypeKind kIntegral[] = {
      DataTypeKind::kLogic,   DataTypeKind::kReg,      DataTypeKind::kBit,
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kInteger,  DataTypeKind::kTime};
  return std::ranges::find(kIntegral, kind) != std::end(kIntegral);
}

std::optional<std::vector<RtlirUnpackedDim>> DataTypeDims(const DataType& type,
                                                          const ScopeMap& scope,
                                                          int depth) {
  RangeExprs ranges;
  if (type.packed_dim_left != nullptr && type.packed_dim_right != nullptr) {
    ranges.emplace_back(type.packed_dim_left, type.packed_dim_right);
  }
  ranges.insert(ranges.end(), type.extra_packed_dims.begin(),
                type.extra_packed_dims.end());
  if (!ranges.empty()) return FoldRanges(ranges, scope);
  if (type.kind == DataTypeKind::kNamed) {
    const DataType* named = RegisteredTypedef(type.type_name);
    if (named == nullptr || depth > 16) return std::nullopt;
    return DataTypeDims(*named, scope, depth + 1);
  }
  bool packed_aggregate =
      type.is_packed &&
      (type.kind == DataTypeKind::kStruct || type.kind == DataTypeKind::kUnion);
  if (!IsIntegralKind(type.kind) && !packed_aggregate) return std::nullopt;
  int64_t width = RegisteredTypeWidth(type, scope);
  return std::vector<RtlirUnpackedDim>{RtlirUnpackedDim{width - 1, 0}};
}

std::optional<RangeExprs> KeywordRanges(const Expr* arg) {
  if (arg->kind == ExprKind::kIdentifier) {
    bool vector =
        arg->text == "bit" || arg->text == "logic" || arg->text == "reg";
    return vector ? std::optional<RangeExprs>(RangeExprs{}) : std::nullopt;
  }
  if (arg->kind != ExprKind::kSelect || arg->base == nullptr ||
      arg->index_end == nullptr || arg->is_part_select_plus ||
      arg->is_part_select_minus) {
    return std::nullopt;
  }
  auto ranges = KeywordRanges(arg->base);
  if (ranges) ranges->emplace_back(arg->index, arg->index_end);
  return ranges;
}

std::optional<QueryDims> TypeQueryDims(
    std::optional<std::vector<RtlirUnpackedDim>> dims) {
  if (!dims) return std::nullopt;
  return QueryDims{*std::move(dims), 0, true};
}

std::optional<std::vector<RtlirUnpackedDim>> ParamPackedDims(
    const RtlirParamDecl& param, const ScopeMap& scope) {
  if (param.is_real_value || param.is_string_value || param.is_type_param) {
    return std::nullopt;
  }
  if (param.decl_type != nullptr && !param.decl_type_implicit) {
    return DataTypeDims(*param.decl_type, scope, 0);
  }
  int64_t width = ParamStorageShapeOf(param).width;
  return std::vector<RtlirUnpackedDim>{RtlirUnpackedDim{width - 1, 0}};
}

std::optional<QueryDims> ParamDims(const RtlirParamDecl& param) {
  ScopeMap scope = RegisteredModuleScope();
  QueryDims out;
  if (param.unpacked_dims != nullptr) {
    for (const Expr* dim : *param.unpacked_dims) {
      auto folded = FoldUnpackedDimBounds(dim, scope);
      if (!folded) return std::nullopt;
      out.dims.push_back(*folded);
    }
  }
  out.unpacked = out.dims.size();
  auto packed = ParamPackedDims(param, scope);
  out.has_packed = packed.has_value();
  if (packed) out.dims.insert(out.dims.end(), packed->begin(), packed->end());
  return out;
}

std::optional<QueryDims> VariableDims(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& var : mod->variables) {
    if (var.name == name && var.num_unpacked_dims != 0 &&
        var.unpacked_dims.size() == var.num_unpacked_dims) {
      return QueryDims{var.unpacked_dims, var.unpacked_dims.size(), false};
    }
  }
  return std::nullopt;
}

std::optional<QueryDims> QueryDimsOf(const Expr* arg, const ScopeMap& scope) {
  if (arg->kind == ExprKind::kTypeRef && arg->type_value != nullptr) {
    return TypeQueryDims(DataTypeDims(*arg->type_value, scope, 0));
  }
  if (auto ranges = KeywordRanges(arg)) {
    if (ranges->empty()) return QueryDims{{RtlirUnpackedDim{0, 0}}, 0, true};
    return TypeQueryDims(FoldRanges(*ranges, scope));
  }
  if (arg->kind != ExprKind::kIdentifier) return std::nullopt;
  if (auto dim = KeywordDim(arg->text)) return QueryDims{{*dim}, 0, true};
  if (const DataType* type = RegisteredTypedef(arg->text)) {
    return TypeQueryDims(DataTypeDims(*type, scope, 0));
  }
  if (const RtlirParamDecl* param = RegisteredParamNamed(arg->text)) {
    return ParamDims(*param);
  }
  return VariableDims(arg->text);
}

int64_t DimensionAnswer(std::string_view callee, const RtlirUnpackedDim& dim) {
  if (callee == "$left") return dim.left;
  if (callee == "$right") return dim.right;
  if (callee == "$low") return dim.Low();
  if (callee == "$high") return dim.left > dim.right ? dim.left : dim.right;
  if (callee == "$increment") return dim.left >= dim.right ? 1 : -1;
  return dim.Size();
}

}  // namespace

std::optional<RtlirUnpackedDim> FoldUnpackedDimBounds(const Expr* dim,
                                                      const ScopeMap& scope) {
  if (dim == nullptr) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs, scope);
    auto rv = ConstEvalInt(dim->rhs, scope);
    if (!lv || !rv) return std::nullopt;
    return RtlirUnpackedDim{*lv, *rv};
  }
  auto sv = ConstEvalInt(dim, scope);
  if (!sv || *sv <= 0) return std::nullopt;
  return RtlirUnpackedDim{0, *sv - 1};
}

bool IsDynamicallySized(const Expr* arg) {
  if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
  if (const RtlirParamDecl* param = RegisteredParamNamed(arg->text)) {
    if (param->unpacked_dims == nullptr) return false;
    return std::ranges::any_of(*param->unpacked_dims, [](const Expr* dim) {
      return dim == nullptr || (dim->kind == ExprKind::kIdentifier &&
                                (dim->text == "$" || dim->text == "*"));
    });
  }
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return false;
  return std::ranges::any_of(mod->variables, [&](const RtlirVariable& var) {
    return var.name == arg->text &&
           (var.is_dynamic || var.is_queue || var.is_assoc || var.is_string);
  });
}

bool IsArrayQueryFunction(std::string_view name) {
  return name == "$dimensions" || name == "$unpacked_dimensions" ||
         name == "$left" || name == "$right" || name == "$low" ||
         name == "$high" || name == "$increment" || name == "$size";
}

std::optional<int64_t> EvalConstArrayQuery(const Expr* expr,
                                           const ScopeMap& scope) {
  if (expr->args.empty() || expr->args[0] == nullptr) return std::nullopt;
  auto dims = QueryDimsOf(expr->args[0], scope);
  if (!dims) return std::nullopt;
  if (expr->callee == "$dimensions") {
    if (!dims->has_packed) return std::nullopt;
    return static_cast<int64_t>(dims->dims.size());
  }
  if (expr->callee == "$unpacked_dimensions") {
    return static_cast<int64_t>(dims->unpacked);
  }
  std::optional<int64_t> n =
      expr->args.size() >= 2 ? ConstEvalInt(expr->args[1], scope) : 1;
  if (!n || *n < 1 || static_cast<size_t>(*n) > dims->dims.size()) {
    return std::nullopt;
  }
  return DimensionAnswer(expr->callee, dims->dims[static_cast<size_t>(*n - 1)]);
}

}  // namespace delta
