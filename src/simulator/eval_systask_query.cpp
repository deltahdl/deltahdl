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

// Classification of the first argument's outermost (slowest varying)
// dimension, used to compute the array query results.
struct QueryArgInfo {
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  const ArrayInfo* arr = nullptr;
  bool dynamic_outer = false;
  bool has_unpacked = false;
  uint32_t elem_width = 32;  // packed element dimension [n-1:0]
  bool is_real = false;
  bool is_string = false;
};

// Resolve the first argument to an unpacked container (if any) and determine
// the width/kind of its packed element dimension. §20.7: a string is a nonarray
// type equivalent to a simple bit vector (one packed dimension); a real type
// contributes no packed dimension.
static QueryArgInfo ClassifyQueryArg(const Expr* arg0, SimContext& ctx,
                                     Arena& arena) {
  QueryArgInfo info;
  if (arg0 && arg0->kind == ExprKind::kIdentifier) {
    info.assoc = ctx.FindAssocArray(arg0->text);
    info.queue = ctx.FindQueue(arg0->text);
    info.arr = ctx.FindArrayInfo(arg0->text);
  }
  info.dynamic_outer =
      info.queue != nullptr ||
      (info.arr != nullptr && (info.arr->is_dynamic || info.arr->is_queue));
  info.has_unpacked =
      info.assoc != nullptr || info.queue != nullptr || info.arr != nullptr;

  if (info.assoc) {
    info.elem_width = info.assoc->elem_width;
  } else if (info.queue) {
    info.elem_width = info.queue->elem_width;
  } else if (info.arr) {
    info.elem_width = info.arr->elem_width;
  } else if (arg0 && arg0->kind == ExprKind::kIdentifier &&
             ctx.IsStringVariable(arg0->text)) {
    info.is_string = true;
  } else if (arg0) {
    auto val = EvalExpr(arg0, ctx, arena);
    info.elem_width = val.width;
    info.is_real = val.is_real;
  }
  return info;
}

// Bounds for an associative array dimension with an integral index type.
static QueryDimBounds AssocDimBounds(AssocArrayObject* assoc) {
  QueryDimBounds q;
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
  return q;
}

// Bounds for a queue or dynamic array dimension: indices run 0 .. size-1,
// descending.
static QueryDimBounds DynamicDimBounds(const QueryArgInfo& info) {
  QueryDimBounds q;
  int64_t count = info.queue
                      ? static_cast<int64_t>(info.queue->elements.size())
                      : static_cast<int64_t>(info.arr ? info.arr->size : 0);
  q.left = 0;
  q.right = count - 1;  // -1 when the dimension is currently empty
  q.low = 0;
  q.high = count - 1;
  q.increment = -1;
  q.size = count;
  return q;
}

// Bounds for a fixed-size unpacked dimension with declared bounds.
static QueryDimBounds FixedUnpackedDimBounds(const ArrayInfo* arr) {
  QueryDimBounds q;
  int64_t lo = arr->lo;
  int64_t hi = arr->lo + static_cast<int64_t>(arr->size) - 1;
  q.left = arr->is_descending ? hi : lo;
  q.right = arr->is_descending ? lo : hi;
  q.low = lo;
  q.high = hi;
  q.size = arr->size;
  q.increment = (q.left >= q.right) ? 1 : -1;
  return q;
}

// Bounds for the dim-th unpacked dimension of a multidimensional fixed array,
// where dim is 1-based and dimension 1 is the slowest varying (outermost)
// dimension. dim_los/dim_sizes are stored outermost-first, so index dim-1 names
// dimension dim. Only the outermost dimension carries a tracked direction; the
// inner dimensions' declared extents are recorded low-first, so
// $size/$low/$high are exact for every dimension and $left/$right/$increment
// follow the ascending order in which those inner extents are held.
static QueryDimBounds MultiDimUnpackedDimBounds(const ArrayInfo* arr,
                                                uint32_t dim) {
  QueryDimBounds q;
  int64_t lo = arr->dim_los[dim - 1];
  int64_t hi = lo + static_cast<int64_t>(arr->dim_sizes[dim - 1]) - 1;
  bool descending = (dim == 1) && arr->is_descending;
  q.left = descending ? hi : lo;
  q.right = descending ? lo : hi;
  q.low = lo;
  q.high = hi;
  q.size = arr->dim_sizes[dim - 1];
  q.increment = (q.left >= q.right) ? 1 : -1;
  return q;
}

// Bounds for the packed element dimension [elem_width-1 : 0].
static QueryDimBounds PackedElemDimBounds(uint32_t elem_width) {
  QueryDimBounds q;
  q.left = static_cast<int64_t>(elem_width) - 1;
  q.right = 0;
  q.low = 0;
  q.high = static_cast<int64_t>(elem_width) - 1;
  q.size = elem_width;
  q.increment = (q.left >= q.right) ? 1 : -1;
  return q;
}

// The number of unpacked dimensions the first argument contributes. A fixed
// multidimensional array carries every extent in dim_sizes; every other
// unpacked container (single fixed dimension, queue, dynamic array, or
// associative array) contributes exactly one.
static uint32_t UnpackedDimCount(const QueryArgInfo& info) {
  if (info.arr && info.arr->dim_sizes.size() >= 2)
    return static_cast<uint32_t>(info.arr->dim_sizes.size());
  return info.has_unpacked ? 1 : 0;
}

// Compute the bounds reported for the queried dimension. Dimensions are
// numbered slowest-varying first: dimensions 1..unpacked_dims are the unpacked
// dimensions (outermost first) and the packed element dimension, when present,
// is the next (last) dimension.
static QueryDimBounds ComputeQueryDimBounds(const QueryArgInfo& info,
                                            uint32_t dim,
                                            uint32_t unpacked_dims) {
  if (dim <= unpacked_dims) {
    if (info.assoc) return AssocDimBounds(info.assoc);
    if (info.dynamic_outer) return DynamicDimBounds(info);
    if (info.arr && info.arr->dim_sizes.size() >= 2)
      return MultiDimUnpackedDimBounds(info.arr, dim);
    if (info.arr) return FixedUnpackedDimBounds(info.arr);
  }
  return PackedElemDimBounds(info.elem_width);
}

// Count the packed and unpacked dimensions contributed by the first argument.
// A simple bit-vector type (string included) contributes one packed dimension;
// a real (or any other nonvector) type contributes none. An array contributes
// one unpacked dimension per declared unpacked extent.
static uint32_t CountTotalDims(const QueryArgInfo& info,
                               uint32_t& unpacked_dims) {
  uint32_t packed_dims =
      (info.is_string || (info.elem_width > 0 && !info.is_real)) ? 1 : 0;
  unpacked_dims = UnpackedDimCount(info);
  return packed_dims + unpacked_dims;
}

// Produce the integer result for a per-dimension query ($left/$right/...).
static Logic4Vec SelectDimQueryResult(std::string_view name,
                                      const QueryDimBounds& q, Arena& arena) {
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

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  const Expr* arg0 = expr->args.empty() ? nullptr : expr->args[0];

  // Classify the first argument's outermost (slowest varying) dimension.
  QueryArgInfo info = ClassifyQueryArg(arg0, ctx, arena);

  uint32_t unpacked_dims = 0;
  uint32_t total_dims = CountTotalDims(info, unpacked_dims);

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

  // Dimensions are numbered slowest-varying first: the unpacked dimensions
  // (outermost = dimension 1) precede the packed element dimension, which is
  // the last dimension when the element is a bit vector.
  QueryDimBounds q = ComputeQueryDimBounds(info, dim, unpacked_dims);
  return SelectDimQueryResult(name, q, arena);
}

}  // namespace delta
