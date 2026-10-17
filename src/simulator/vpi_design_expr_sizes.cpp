#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <vector>

#include "common/types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The value of `expr` where it is a constant, which a range or a count is
// written as; null for any other expression.
const Variable* ConstantValue(const VpiObject* expr) {
  return expr != nullptr && expr->type == vpiConstant ? expr->var : nullptr;
}

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

// §11.6.1 Table 11-21: the self-determined width of the operation `op` over
// operands of the sizes `sizes`, in order; 0 for one the table does not
// size.
int OperationWidth(const VpiObject& op, const std::vector<int>& sizes,
                   const std::vector<VpiHandle>& operands) {
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
    case vpiMultiConcatOp: {
      const Variable* count = ConstantValue(operands.front());
      if (count == nullptr) return 0;
      int sum = 0;
      for (std::size_t i = 1; i < sizes.size(); ++i) sum += sizes[i];
      return static_cast<int>(count->value.ToUint64()) * sum;
    }
    default:
      return *std::ranges::max_element(sizes);
  }
}

// §11.5.1: the width a part select of constant bounds, or an indexed part
// select of constant width, selects; 0 where they are not constants.
int PartSelectWidth(const VpiObject& select) {
  if (select.type == vpiIndexedPartSelect) {
    const Variable* width = ConstantValue(select.width_expr);
    return width != nullptr ? static_cast<int>(width->value.ToUint64()) : 0;
  }
  const Variable* left = ConstantValue(select.left_range);
  const Variable* right = ConstantValue(select.right_range);
  if (left == nullptr || right == nullptr) return 0;
  const auto kSpan = static_cast<int64_t>(left->value.ToUint64()) -
                     static_cast<int64_t>(right->value.ToUint64());
  return static_cast<int>(std::abs(kSpan) + 1);
}

}  // namespace

void VpiSizeExpression(VpiObject* expr) {
  if (expr == nullptr || expr->size != 0) return;
  if (expr->type == vpiPartSelect || expr->type == vpiIndexedPartSelect) {
    expr->size = PartSelectWidth(*expr);
    return;
  }
  if (expr->type != vpiOperation) return;
  const std::vector<VpiHandle> kOperands = VpiOperationOperands(expr);
  std::vector<int> sizes;
  sizes.reserve(kOperands.size());
  for (const VpiObject* operand : kOperands) sizes.push_back(operand->size);
  expr->size = OperationWidth(*expr, sizes, kOperands);
}

}  // namespace delta
