#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <vector>

#include "parser/ast_expr.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assigns_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §11.6.1 Table 11-21: an operator whose result is one bit wide.
bool IsOneBitOp(int op_type) {
  switch (op_type) {
    case vpiNotOp:
    case vpiUnaryAndOp:
    case vpiUnaryNandOp:
    case vpiUnaryOrOp:
    case vpiUnaryNorOp:
    case vpiUnaryXorOp:
    case vpiUnaryXNorOp:
    case vpiEqOp:
    case vpiNeqOp:
    case vpiCaseEqOp:
    case vpiCaseNeqOp:
    case vpiWildEqOp:
    case vpiWildNeqOp:
    case vpiGtOp:
    case vpiGeOp:
    case vpiLtOp:
    case vpiLeOp:
    case vpiLogAndOp:
    case vpiLogOrOp:
    case vpiImplyOp:
    case vpiInsideOp:
      return true;
    default:
      return false;
  }
}

// §11.6.1 Table 11-21: an operator whose result is as wide as its left
// operand, the right one being self-determined.
bool IsLeftWidthOp(int op_type) {
  switch (op_type) {
    case vpiLShiftOp:
    case vpiRShiftOp:
    case vpiArithLShiftOp:
    case vpiArithRShiftOp:
    case vpiPowerOp:
      return true;
    default:
      return false;
  }
}

// §6.11 Table 6-8 and §6.12: the width of the built-in type a cast names by
// keyword, 0 for one with no bit width (§37.59 leaves it to the typespec). A
// bit or logic typespec a size, signing or const cast makes from its operand
// records its own width (§6.24.1).
int CastWidth(const VpiObject& op) {
  for (const VpiObject* child : op.children) {
    switch (child->type) {
      case vpiBitTypespec:
      case vpiLogicTypespec:
        return child->size != 0 ? child->size : 1;
      case vpiByteTypespec:
        return 8;
      case vpiShortIntTypespec:
        return 16;
      case vpiIntTypespec:
      case vpiIntegerTypespec:
        return 32;
      case vpiLongIntTypespec:
      case vpiTimeTypespec:
        return 64;
      default:
        break;
    }
  }
  return 0;
}

// §11.4.12.1 with §11.6.1 Table 11-21: the width of the replication `expr`,
// its count, a constant expression, times the widths of the expressions it
// repeats, which follow the count among `sizes` (§37.59 detail 1); 0 where
// the count does not fold.
int ReplicationWidth(const Expr& expr, const std::vector<int>& sizes,
                     const AssignBuild& build) {
  const std::optional<int64_t> kCount =
      ElaborationConstant(expr.repeat_count, build);
  if (!kCount) return 0;
  int sum = 0;
  for (std::size_t i = 1; i < sizes.size(); ++i) sum += sizes[i];
  return static_cast<int>(*kCount) * sum;
}

// §11.6.1 Table 11-21: the self-determined width of the operation `op`, built
// for `expr`, over operands of the sizes `sizes`, in order; 0 for one the
// table does not size.
int OperationWidth(const VpiObject& op, const std::vector<int>& sizes,
                   const Expr& expr, const AssignBuild& build) {
  if (sizes.empty()) return 0;
  if (IsOneBitOp(op.op_type)) return 1;
  if (IsLeftWidthOp(op.op_type)) return sizes.front();
  switch (op.op_type) {
    case vpiCastOp:
      return CastWidth(op) != 0 ? CastWidth(op) : sizes.front();
    case vpiConditionOp:
      return sizes.size() == 3 ? std::max(sizes[1], sizes[2]) : 0;
    case vpiConcatOp: {
      int sum = 0;
      for (int size : sizes) sum += size;
      return sum;
    }
    case vpiMultiConcatOp:
      return ReplicationWidth(expr, sizes, build);
    default:
      return *std::ranges::max_element(sizes);
  }
}

// §11.5.1: the width the select `expr` selects, the span of a part select's
// bounds or an indexed part select's width, each a constant expression; 0
// where one does not fold.
int SelectWidth(const Expr& expr, const AssignBuild& build) {
  const std::optional<int64_t> kSecond =
      ElaborationConstant(expr.index_end, build);
  if (expr.is_part_select_plus || expr.is_part_select_minus) {
    return static_cast<int>(kSecond.value_or(0));
  }
  const std::optional<int64_t> kFirst = ElaborationConstant(expr.index, build);
  if (!kFirst || !kSecond) return 0;
  return static_cast<int>(std::abs(*kFirst - *kSecond) + 1);
}

}  // namespace

void VpiSizeExpression(VpiObject* obj, const Expr& expr,
                       const AssignBuild& build) {
  if (obj == nullptr || obj->size != 0) return;
  if (obj->type == vpiPartSelect || obj->type == vpiIndexedPartSelect) {
    obj->size = SelectWidth(expr, build);
    return;
  }
  if (obj->type != vpiOperation) return;
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(obj);
  std::vector<int> sizes;
  sizes.reserve(kOperands.size());
  for (const VpiObject* operand : kOperands) sizes.push_back(operand->size);
  obj->size = OperationWidth(*obj, sizes, expr, build);
}

}  // namespace delta
