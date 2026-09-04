#include "elaborator/elaborator_dpi_signature.h"

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "parser/ast.h"
#include "parser/ast_expr.h"

namespace delta {

namespace {

// A dimension written as a range, `[left:right]`, which is the only form a
// packed dimension takes.
DpiDimension DimensionFromRange(const Expr* left, const Expr* right) {
  DpiDimension dim;
  dim.left = ConstEvalInt(left);
  dim.right = ConstEvalInt(right);
  return dim;
}

// An unpacked dimension, which Parser::ParseUnpackedDims records as a null
// pointer for the empty-bracket form, as a `:` binary for the range form, and
// as a bare expression for the size form.
DpiDimension DimensionFromUnpacked(const Expr* written) {
  DpiDimension dim;
  if (written == nullptr) {
    dim.is_unsized = true;
    return dim;
  }
  if (written->kind == ExprKind::kBinary && written->op == TokenKind::kColon) {
    return DimensionFromRange(written->lhs, written->rhs);
  }
  // §7.4.2: the size form `[N]` declares the range `[0:N-1]`, so recording it
  // that way is what makes `[4]` and `[0:3]` one dimension.
  auto size = ConstEvalInt(written);
  if (size.has_value()) {
    dim.left = 0;
    dim.right = *size - 1;
  }
  return dim;
}

// The direction and shape of every formal, in the order they were declared.
// §35.5.4 puts that list into an import's signature and §35.4 into an export's,
// so both builders below take it from here.
std::vector<std::pair<Direction, DpiTypeShape>> BuildDpiArgShapes(
    const ModuleItem* item) {
  std::vector<std::pair<Direction, DpiTypeShape>> args;
  args.reserve(item->func_args.size());
  for (const auto& arg : item->func_args) {
    args.emplace_back(arg.direction,
                      BuildDpiTypeShape(arg.data_type, arg.unpacked_dims));
  }
  return args;
}

}  // namespace

std::string_view DpiLinkageName(const ModuleItem* item) {
  return item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
}

DpiTypeShape BuildDpiTypeShape(const DataType& type,
                               const std::vector<Expr*>& unpacked_dims) {
  DpiTypeShape shape;
  shape.kind = type.kind;
  shape.has_unsized_packed_dim = type.has_unsized_packed_dim;
  if (type.packed_dim_left != nullptr) {
    shape.packed_dims.push_back(
        DimensionFromRange(type.packed_dim_left, type.packed_dim_right));
  }
  for (const auto& [left, right] : type.extra_packed_dims) {
    shape.packed_dims.push_back(DimensionFromRange(left, right));
  }
  shape.unpacked_dims.reserve(unpacked_dims.size());
  for (const auto* written : unpacked_dims) {
    shape.unpacked_dims.push_back(DimensionFromUnpacked(written));
  }
  return shape;
}

DpiSignatureKey BuildDpiSignature(const ModuleItem* item) {
  DpiSignatureKey key;
  key.return_type = BuildDpiTypeShape(item->return_type, {});
  key.is_pure = item->dpi_is_pure;
  key.is_context = item->dpi_is_context;
  key.is_task = item->dpi_is_task;
  key.spec_string = item->dpi_spec_string;
  key.args = BuildDpiArgShapes(item);
  return key;
}

bool DpiSignaturesMatch(const DpiSignatureKey& a, const DpiSignatureKey& b) {
  return a.return_type == b.return_type && a.is_pure == b.is_pure &&
         a.is_context == b.is_context && a.is_task == b.is_task &&
         a.spec_string == b.spec_string && a.args == b.args;
}

DpiExportSignature BuildDpiExportSignature(const ModuleItem* callable) {
  DpiExportSignature key;
  key.return_type = BuildDpiTypeShape(callable->return_type, {});
  key.is_task = callable->kind == ModuleItemKind::kTaskDecl;
  key.args = BuildDpiArgShapes(callable);
  return key;
}

}  // namespace delta
