#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_element_shape.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static uint32_t ElementQueueLevels(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims) {
  const std::vector<Expr*>& dims = item->unpacked_dims;
  if (dims.size() >= 2) return QueueLevelsFrom(dims, 1);
  if (dims.size() != 1 || item->data_type.kind != DataTypeKind::kNamed)
    return 0;
  auto it = td_array_dims.find(item->data_type.type_name);
  return it == td_array_dims.end() ? 0 : QueueLevelsFrom(it->second, 0);
}

static std::optional<RtlirFixedDim> FixedDimOf(const Expr* dim,
                                               const ScopeMap& scope) {
  if (dim == nullptr || IsQueueDim(dim)) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs, scope);
    auto rv = ConstEvalInt(dim->rhs, scope);
    if (!lv || !rv) return std::nullopt;
    return RtlirFixedDim{static_cast<uint32_t>(std::abs(*lv - *rv) + 1),
                         std::min(*lv, *rv), *lv > *rv};
  }
  auto size = ConstEvalInt(dim, scope);
  if (!size || *size <= 0) return std::nullopt;
  return RtlirFixedDim{static_cast<uint32_t>(*size), 0, false};
}

static void RecordFixedElementArray(const ModuleItem* item,
                                    const ScopeMap& scope, bool first_is_assoc,
                                    RtlirElementShape& shape) {
  const std::vector<Expr*>& dims = item->unpacked_dims;
  if (dims.size() < 2) return;
  size_t first_fixed = 1;
  if (dims[0] != nullptr && !IsQueueDim(dims[0]) && !first_is_assoc) {
    if (dims[1] != nullptr && !IsQueueDim(dims[1])) return;
    first_fixed = 2;
  }
  if (first_fixed >= dims.size()) return;
  std::vector<RtlirFixedDim> fixed;
  for (size_t i = first_fixed; i < dims.size(); ++i) {
    std::optional<RtlirFixedDim> dim = FixedDimOf(dims[i], scope);
    if (!dim) return;
    fixed.push_back(*dim);
  }
  shape.array_size = fixed[0].size;
  shape.array_lo = fixed[0].lo;
  shape.array_descending = fixed[0].descending;
  shape.inner_array_dims.assign(fixed.begin() + 1, fixed.end());
}

void ElaborateUnpackedDims(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims,
    const UnpackedDimContext& ctx, RtlirVariable& var) {
  ComputeUnpackedDims(item->unpacked_dims, var, ctx);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);
  const uint32_t kQueueLevels = ElementQueueLevels(item, td_array_dims);
  var.elements_are_queues = kQueueLevels > 0;
  var.element.nested_queue_levels = kQueueLevels > 0 ? kQueueLevels - 1 : 0;
  RecordFixedElementArray(item, ctx.scope, var.is_assoc, var.element);
  if (var.element.array_size > 0) var.elements_are_queues = true;
  if (!var.element.inner_array_dims.empty()) {
    var.element.nested_queue_levels =
        static_cast<uint32_t>(var.element.inner_array_dims.size());
  }
}

}  // namespace delta
