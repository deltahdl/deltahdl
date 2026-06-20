#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// Build an all-x integer result. §20.7 calls for 'x whenever a query has no
// well-defined answer (a dimensionless first argument or an out-of-range
// dimension index).
static Logic4Vec MakeUnknownInt(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  uint64_t mask = (width < 64) ? ((uint64_t{1} << width) - 1) : ~uint64_t{0};
  if (vec.nwords > 0) {
    vec.words[0].aval = mask;
    vec.words[0].bval = mask;
  }
  return vec;
}

// Bounds of a single array dimension, as the array query functions report them.
struct QueryDimBounds {
  int64_t left = 0;
  int64_t right = 0;
  int64_t low = 0;
  int64_t high = 0;
  int64_t increment = 1;
  int64_t size = 0;
  bool low_high_unknown = false;  // $low/$high are 'x for an empty assoc array
};

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  const Expr* arg0 = expr->args.empty() ? nullptr : expr->args[0];

  // Classify the first argument's outermost (slowest varying) dimension.
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  const ArrayInfo* arr = nullptr;
  if (arg0 && arg0->kind == ExprKind::kIdentifier) {
    assoc = ctx.FindAssocArray(arg0->text);
    queue = ctx.FindQueue(arg0->text);
    arr = ctx.FindArrayInfo(arg0->text);
  }
  bool dynamic_outer = queue != nullptr ||
                       (arr != nullptr && (arr->is_dynamic || arr->is_queue));
  bool has_unpacked = assoc != nullptr || queue != nullptr || arr != nullptr;

  // Width of the packed element dimension (the [n-1:0] of an integer type).
  uint32_t elem_width = 32;
  bool is_real = false;
  bool is_string = false;
  if (assoc) {
    elem_width = assoc->elem_width;
  } else if (queue) {
    elem_width = queue->elem_width;
  } else if (arr) {
    elem_width = arr->elem_width;
  } else if (arg0 && arg0->kind == ExprKind::kIdentifier &&
             ctx.IsStringVariable(arg0->text)) {
    // §20.7: a string is a nonarray type that is equivalent to a simple bit
    // vector, so it always contributes exactly one packed dimension regardless
    // of how many characters it currently holds.
    is_string = true;
  } else if (arg0) {
    auto val = EvalExpr(arg0, ctx, arena);
    elem_width = val.width;
    is_real = val.is_real;
  }

  // A simple bit-vector type (string included) contributes one packed
  // dimension; a real (or any other nonvector) type contributes none.
  uint32_t packed_dims = (is_string || (elem_width > 0 && !is_real)) ? 1 : 0;
  uint32_t unpacked_dims = has_unpacked ? 1 : 0;
  uint32_t total_dims = packed_dims + unpacked_dims;

  if (name == "$dimensions") return MakeLogic4VecVal(arena, 32, total_dims);
  if (name == "$unpacked_dimensions")
    return MakeLogic4VecVal(arena, 32, unpacked_dims);

  // §20.7: 'x when the first argument has no dimensions ($dimensions would be
  // 0) or when the optional dimension index is out of range.
  if (total_dims == 0) return MakeUnknownInt(arena, 32);
  uint32_t dim = 1;
  if (expr->args.size() > 1)
    dim = static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  if (dim < 1 || dim > total_dims) return MakeUnknownInt(arena, 32);

  // Dimension 1 is the slowest varying. When an unpacked dimension is present
  // it is dimension 1 and the packed element dimension (if any) is dimension 2;
  // otherwise the packed dimension is dimension 1.
  bool query_unpacked = has_unpacked && dim == 1;

  QueryDimBounds q;
  if (query_unpacked && assoc) {
    // Associative array dimension with an integral index type.
    uint32_t iw = assoc->index_width ? assoc->index_width : 32;
    q.left = 0;
    q.right = (iw >= 64) ? static_cast<int64_t>(~uint64_t{0})
                         : static_cast<int64_t>((uint64_t{1} << iw) - 1);
    q.increment = -1;
    q.size = assoc->Size();
    if (assoc->int_data.empty()) {
      q.low_high_unknown = true;
    } else {
      q.low = assoc->int_data.begin()->first;
      q.high = assoc->int_data.rbegin()->first;
    }
  } else if (query_unpacked && dynamic_outer) {
    // Queue or dynamic array dimension: indices run 0 .. size-1, descending.
    int64_t count = queue ? static_cast<int64_t>(queue->elements.size())
                          : static_cast<int64_t>(arr ? arr->size : 0);
    q.left = 0;
    q.right = count - 1;  // -1 when the dimension is currently empty
    q.low = 0;
    q.high = count - 1;
    q.increment = -1;
    q.size = count;
  } else if (query_unpacked && arr) {
    // Fixed-size unpacked dimension with declared bounds.
    int64_t lo = arr->lo;
    int64_t hi = arr->lo + static_cast<int64_t>(arr->size) - 1;
    q.left = arr->is_descending ? hi : lo;
    q.right = arr->is_descending ? lo : hi;
    q.low = lo;
    q.high = hi;
    q.size = arr->size;
    q.increment = (q.left >= q.right) ? 1 : -1;
  } else {
    // Packed element dimension [elem_width-1 : 0].
    q.left = static_cast<int64_t>(elem_width) - 1;
    q.right = 0;
    q.low = 0;
    q.high = static_cast<int64_t>(elem_width) - 1;
    q.size = elem_width;
    q.increment = (q.left >= q.right) ? 1 : -1;
  }

  auto as_int = [&](int64_t v) {
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(v));
  };
  if (name == "$left") return as_int(q.left);
  if (name == "$right") return as_int(q.right);
  if (name == "$increment") return as_int(q.increment);
  if (name == "$low")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.low);
  if (name == "$high")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.high);
  return as_int(q.size);  // $size
}

}  // namespace delta
