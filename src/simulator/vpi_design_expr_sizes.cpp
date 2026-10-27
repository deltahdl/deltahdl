#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <optional>
#include <string>
#include <vector>

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

// §11.5.1 and §11.4.12.1: the value of `constant`, a select's bound or width
// or a replication's count, which those clauses make a constant expression:
// its fold, where ElaborationConstant folds it, and otherwise its value where
// the source wrote it, in the instance and the generate blocks `build` stands
// in, as for $bits of a variable (§20.6.2), an array query (§20.7) or a
// constant function call (§13.4.3), all constants §11.2.1 admits.
int64_t ConstantWhereWritten(const Expr* constant, const AssignBuild& build) {
  const std::optional<int64_t> kFolded = ElaborationConstant(constant, build);
  if (kFolded) return *kFolded;
  const VpiExprScope kScope{
      constant, VpiFlatName(build.names.prefix, ""),
      std::vector<std::string>(build.names.gen.begin(), build.names.gen.end())};
  return SelectBoundValue(VpiEvaluateWhereWritten(kScope, *build.sim));
}

// §11.4.12.1 with §11.6.1 Table 11-21: the width of the replication `expr`,
// its count times the widths of the expressions it repeats, which follow the
// count among `sizes` (§37.59 detail 1).
int ReplicationWidth(const Expr& expr, const std::vector<int>& sizes,
                     const AssignBuild& build) {
  int sum = 0;
  for (std::size_t i = 1; i < sizes.size(); ++i) sum += sizes[i];
  return static_cast<int>(ConstantWhereWritten(expr.repeat_count, build)) * sum;
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
    case vpiConcatOp:
      return std::accumulate(sizes.begin(), sizes.end(), 0);
    case vpiMultiConcatOp:
      return ReplicationWidth(expr, sizes, build);
    default:
      return *std::ranges::max_element(sizes);
  }
}

// §11.5.1: the width the select `expr` selects, the span of a part select's
// bounds or an indexed part select's width.
int SelectWidth(const Expr& expr, const AssignBuild& build) {
  const int64_t kSecond = ConstantWhereWritten(expr.index_end, build);
  if (expr.is_part_select_plus || expr.is_part_select_minus) {
    return static_cast<int>(kSecond);
  }
  const int64_t kFirst = ConstantWhereWritten(expr.index, build);
  return static_cast<int>(std::abs(kFirst - kSecond) + 1);
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
