#include <algorithm>
#include <cstdint>
#include <cstdlib>
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

// §7.4 with §7.5 and §7.10 (printed pages 153, 157 and 169): how many levels
// of queues each element of the array `item` declares holds, counting the
// element itself, 0 where the element is no queue -- its dimensions after the
// first are each `[$]` or `[]`, `int aq[string][$]` or `int arr[2][][]`, or
// its one dimension's element type names a typedef whose own unpacked
// dimensions are, `q_t d[]` under `typedef int q_t[$];`, the typedef's
// dimensions being part of the type it names (§6.18).
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

// §7.10 and §7.5 with §7.4 (printed pages 169, 157 and 153): where each
// element of the queue or dynamic array `item` declares is a fixed-size
// array, `int q[$][3]` or `int d[][1:3]`, records into `shape` how many
// elements it holds and its bounds, each such element being kept as a queue
// of that many elements (RtlirElementShape::array_size); nothing for any
// other declaration.
static void RecordFixedElementArray(const ModuleItem* item,
                                    const ScopeMap& scope,
                                    RtlirElementShape& shape) {
  const std::vector<Expr*>& dims = item->unpacked_dims;
  if (dims.size() != 2 || dims[1] == nullptr || IsQueueDim(dims[1])) return;
  if (dims[0] != nullptr && !IsQueueDim(dims[0])) return;
  const Expr* dim = dims[1];
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs, scope);
    auto rv = ConstEvalInt(dim->rhs, scope);
    if (!lv || !rv) return;
    shape.array_size = static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
    shape.array_lo = std::min(*lv, *rv);
    shape.array_descending = *lv > *rv;
    return;
  }
  auto size = ConstEvalInt(dim, scope);
  if (size && *size > 0) shape.array_size = static_cast<uint32_t>(*size);
}

// §7.4 (printed pages 153-156): what the unpacked dimensions `item` declares
// make of `var` -- each dimension's kind and extent (ComputeUnpackedDims), a
// dynamic array's size from its initializer (InferDynArraySize), and whether
// and how its elements are arrays themselves (ElementQueueLevels,
// RecordFixedElementArray) -- the scope in `ctx` folding their bounds.
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
  RecordFixedElementArray(item, ctx.scope, var.element);
  if (var.element.array_size > 0) var.elements_are_queues = true;
}

}  // namespace delta
