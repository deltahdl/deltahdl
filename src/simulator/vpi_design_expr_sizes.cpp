#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <optional>
#include <string>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assigns_internal.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_expr_values.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

int ReplicationWidth(const Expr& expr, const std::vector<int>& sizes,
                     const AssignBuild& build) {
  int sum = 0;
  for (std::size_t i = 1; i < sizes.size(); ++i) sum += sizes[i];
  return static_cast<int>(ConstantWhereWritten(expr.repeat_count, build)) * sum;
}

int OperationWidth(const VpiObject& op, const std::vector<int>& sizes,
                   const Expr& expr, const AssignBuild& build) {
  if (op.op_type == vpiCastOp && CastWidth(op) != 0) return CastWidth(op);
  if (sizes.empty()) return 0;
  if (IsOneBitOp(op.op_type)) return 1;
  if (IsLeftWidthOp(op.op_type)) return sizes.front();
  switch (op.op_type) {
    case vpiConditionOp:
      return sizes.size() == 3 ? std::max(sizes[1], sizes[2]) : 0;
    case vpiConcatOp:
      return std::accumulate(sizes.begin(), sizes.end(), 0);
    case vpiMultiConcatOp:
      return ReplicationWidth(expr, sizes, build);
    default:
      return *std::ranges::max_element(sizes);
  }
}

int SelectWidth(const Expr& expr, const AssignBuild& build) {
  const int64_t kSecond = ConstantWhereWritten(expr.index_end, build);
  if (expr.is_part_select_plus || expr.is_part_select_minus) {
    return static_cast<int>(kSecond);
  }
  const int64_t kFirst = ConstantWhereWritten(expr.index, build);
  return static_cast<int>(std::abs(kFirst - kSecond) + 1);
}

}  // namespace

Logic4Vec ValueWhereWritten(const Expr* expr, const AssignBuild& build) {
  const VpiExprScope kScope{
      expr, VpiFlatName(build.names.prefix, ""),
      std::vector<std::string>(build.names.gen.begin(), build.names.gen.end())};
  return VpiEvaluateWhereWritten(kScope, *build.sim);
}

int64_t ConstantWhereWritten(const Expr* constant, const AssignBuild& build) {
  const std::optional<int64_t> kFolded = ElaborationConstant(constant, build);
  if (kFolded) return *kFolded;
  return SelectBoundValue(ValueWhereWritten(constant, build));
}

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
