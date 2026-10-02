// §20.7 (printed pages 630-632 of IEEE 1800-2023): the array query functions
// are legal in a constant expression on an argument whose dimensions its
// declaration fixes, so they fold at elaboration where those dimensions are
// known here: a built-in or typedef'd data type, a parameter array and a
// variable of the module being elaborated.

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

// The dimensions of a query's argument, slowest varying first (§20.7), with
// how many of them are unpacked and whether the list holds the packed ones
// too, which a parameter array and a variable leave out.
struct QueryDims {
  std::vector<RtlirUnpackedDim> dims;
  size_t unpacked = 0;
  bool has_packed = true;
};

using RangeExprs = std::vector<std::pair<const Expr*, const Expr*>>;

// The dimensions `[l:r]` of each pair in `ranges`, in order; empty where a
// bound does not fold.
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

// §20.7: an integer type with a predefined width is a packed array of one
// `[n-1:0]` dimension.
std::optional<RtlirUnpackedDim> KeywordDim(std::string_view kw) {
  if (kw == "byte") return RtlirUnpackedDim{7, 0};
  if (kw == "shortint") return RtlirUnpackedDim{15, 0};
  if (kw == "int" || kw == "integer") return RtlirUnpackedDim{31, 0};
  if (kw == "longint" || kw == "time") return RtlirUnpackedDim{63, 0};
  return std::nullopt;
}

// The integral types §20.7 gives dimensions to when written with no range.
bool IsIntegralKind(DataTypeKind kind) {
  static constexpr DataTypeKind kIntegral[] = {
      DataTypeKind::kLogic,   DataTypeKind::kReg,      DataTypeKind::kBit,
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kInteger,  DataTypeKind::kTime};
  return std::ranges::find(kIntegral, kind) != std::end(kIntegral);
}

// The packed dimensions `type` writes, or, where it writes none, the one its
// kind implies: an integer atom's `[n-1:0]`, a vector type's single bit and a
// packed structure's or union's width (§20.7). A typedef name answers for the
// type it stands for.
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

// The packed ranges of a vector type keyword written under them, `logic
// [3:0][1:0]`, which the parser holds as a select of a select of the keyword,
// outermost range written first; empty where `arg` is no such type.
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

// A data type as a query's argument: its packed dimensions alone.
std::optional<QueryDims> TypeQueryDims(
    std::optional<std::vector<RtlirUnpackedDim>> dims) {
  if (!dims) return std::nullopt;
  return QueryDims{*std::move(dims), 0, true};
}

// The packed dimensions of a parameter's type: those of the type it was
// declared with, or for one declared with no type the single `[n-1:0]` of the
// value it holds (§6.20.2); none for a real, string or type parameter, which
// holds no bit vector.
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

// A parameter (§20.7 allows the query on it in a constant expression, its
// dimensions being fixed): its unpacked dimensions, then its packed ones.
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

// The unpacked dimensions of a variable of the registered module whose every
// unpacked dimension folded to fixed bounds.
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

// §20.7: the answer of the query `callee` on dimension `dim`.
int64_t DimensionAnswer(std::string_view callee, const RtlirUnpackedDim& dim) {
  if (callee == "$left") return dim.left;
  if (callee == "$right") return dim.right;
  if (callee == "$low") return dim.Low();
  if (callee == "$high") return dim.left > dim.right ? dim.left : dim.right;
  if (callee == "$increment") return dim.left >= dim.right ? 1 : -1;
  return dim.Size();
}

}  // namespace

// §7.4.2 writes a fixed-size unpacked dimension as
// `[ constant_expression : constant_expression ]`, whose first value may be
// greater than, equal to or less than the second, and admits the short form
// where `[size]` means `[0:size-1]`. Both bounds are kept in the order written,
// because §11.5.2 resolves an address against the bounds the declaration gives
// and `[1:4]` and `[4:1]` place their elements at the same addresses in
// opposite order. The bounds are folded in `scope`, since §11.2.1 lets a
// constant expression name a parameter, so `mem [N]` resolves nothing in the
// empty scope; a dimension that folds to nothing is reported to no consumer.
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

bool HasDynamicDimension(const Expr* arg) {
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
           (var.is_dynamic || var.is_queue || var.is_assoc);
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
