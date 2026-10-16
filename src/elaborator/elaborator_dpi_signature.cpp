#include "elaborator/elaborator_dpi_signature.h"

#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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
    const ModuleItem* item, const TypedefMap& typedefs) {
  std::vector<std::pair<Direction, DpiTypeShape>> args;
  args.reserve(item->func_args.size());
  for (const auto& arg : item->func_args) {
    args.emplace_back(
        arg.direction,
        BuildDpiTypeShape(arg.data_type, arg.unpacked_dims, typedefs));
  }
  return args;
}

// The packed dimensions written on `type` itself, outermost first.
void AppendPackedDims(const DataType& type,
                      std::vector<DpiDimension>* packed_dims) {
  if (type.packed_dim_left != nullptr) {
    packed_dims->push_back(
        DimensionFromRange(type.packed_dim_left, type.packed_dim_right));
  }
  for (const auto& [left, right] : type.extra_packed_dims) {
    packed_dims->push_back(DimensionFromRange(left, right));
  }
}

}  // namespace

std::string_view DpiLinkageName(const ModuleItem* item) {
  return item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
}

DpiTypeShape BuildDpiTypeShape(const DataType& type,
                               const std::vector<Expr*>& unpacked_dims,
                               const TypedefMap& typedefs) {
  DpiTypeShape shape;
  // Dimensions written where a typedef name is used stand outside the ones
  // the typedef declared, so they come first: `b_t [3:0]` with `typedef bit
  // [7:0] b_t` is `bit [3:0][7:0]`.
  AppendPackedDims(type, &shape.packed_dims);
  DataType resolved = type;
  if (type.kind == DataTypeKind::kNamed) {
    resolved = ResolveDpiTypeName(type, typedefs);
    AppendPackedDims(resolved, &shape.packed_dims);
  }
  shape.kind = resolved.kind;
  shape.is_signed = resolved.is_signed;
  if (resolved.kind == DataTypeKind::kNamed) {
    shape.unresolved_name = resolved.type_name;
  }
  shape.has_unsized_packed_dim = type.has_unsized_packed_dim;
  shape.unpacked_dims.reserve(unpacked_dims.size());
  for (const auto* written : unpacked_dims) {
    shape.unpacked_dims.push_back(DimensionFromUnpacked(written));
  }
  return shape;
}

DpiSignatureKey BuildDpiSignature(const ModuleItem* item,
                                  const TypedefMap& typedefs) {
  DpiSignatureKey key;
  key.return_type = BuildDpiTypeShape(item->return_type, {}, typedefs);
  key.is_pure = item->dpi_is_pure;
  key.is_context = item->dpi_is_context;
  key.is_task = item->dpi_is_task;
  key.spec_string = item->dpi_spec_string;
  key.args = BuildDpiArgShapes(item, typedefs);
  return key;
}

bool DpiSignaturesMatch(const DpiSignatureKey& a, const DpiSignatureKey& b) {
  return a.return_type == b.return_type && a.is_pure == b.is_pure &&
         a.is_context == b.is_context && a.is_task == b.is_task &&
         a.spec_string == b.spec_string && a.args == b.args;
}

DpiExportSignature BuildDpiExportSignature(const ModuleItem* callable,
                                           const TypedefMap& typedefs) {
  DpiExportSignature key;
  key.return_type = BuildDpiTypeShape(callable->return_type, {}, typedefs);
  key.is_task = callable->kind == ModuleItemKind::kTaskDecl;
  key.args = BuildDpiArgShapes(callable, typedefs);
  return key;
}

}  // namespace delta
