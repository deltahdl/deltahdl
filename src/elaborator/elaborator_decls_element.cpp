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

// §7.4.2: the extent of the fixed-size dimension `dim`, `[l:r]` or `[n]`;
// empty where `dim` is no fixed-size dimension or a bound does not fold.
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

// §7.10 and §7.5 with §7.4 (printed pages 169, 157 and 153): where each
// element of the queue or dynamic array `item` declares is a fixed-size
// array, `int q[$][3]`, `int d[][1:3]` or `int q[$][2][3]`, records into
// `shape` how many elements it holds and its bounds, each such element being
// kept as a queue of that many elements (RtlirElementShape::array_size), and
// the dimensions of a multidimensional element after its first
// (inner_array_dims); nothing for any other declaration.
static void RecordFixedElementArray(const ModuleItem* item,
                                    const ScopeMap& scope,
                                    RtlirElementShape& shape) {
  const std::vector<Expr*>& dims = item->unpacked_dims;
  if (dims.size() < 2) return;
  if (dims[0] != nullptr && !IsQueueDim(dims[0])) return;
  std::vector<RtlirFixedDim> fixed;
  for (size_t i = 1; i < dims.size(); ++i) {
    std::optional<RtlirFixedDim> dim = FixedDimOf(dims[i], scope);
    if (!dim) return;
    fixed.push_back(*dim);
  }
  shape.array_size = fixed[0].size;
  shape.array_lo = fixed[0].lo;
  shape.array_descending = fixed[0].descending;
  shape.inner_array_dims.assign(fixed.begin() + 1, fixed.end());
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
  // §7.4.4: each level of a multidimensional element below its first is a
  // queue of the next dimension's elements.
  if (!var.element.inner_array_dims.empty()) {
    var.element.nested_queue_levels =
        static_cast<uint32_t>(var.element.inner_array_dims.size());
  }
}

}  // namespace delta
