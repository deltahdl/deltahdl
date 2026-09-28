#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
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

// §20.7 with §23.6: the array is named by an identifier, bare or a
// hierarchical reference such as u.mem naming an instance's array; the empty
// name for any other argument.
static std::string QueryArgName(const Expr* arg0) {
  if (arg0 == nullptr) return {};
  if (arg0->kind == ExprKind::kIdentifier) return std::string(arg0->text);
  if (arg0->kind == ExprKind::kMemberAccess && !arg0->is_scope_resolution) {
    return FlattenHierPath(arg0);
  }
  return {};
}

// §20.7 with §8.5: describes into `class_array` the dimension of the unpacked
// array class property `arg0` names, answering whether it names one.
static bool DescribeClassArray(const Expr* arg0, SimContext& ctx, Arena& arena,
                               ArrayInfo& class_array) {
  ClassArrayRef ref;
  if (arg0 == nullptr || !ResolveClassArray(arg0, ctx, arena, ref)) {
    return false;
  }
  class_array.lo = static_cast<uint32_t>(ref.lo);
  class_array.size = ref.size;
  class_array.elem_width = ref.prop->width;
  class_array.is_descending = ref.prop->array_descending;
  class_array.is_dynamic = ref.prop->is_dynamic;
  class_array.is_4state = ref.prop->is_4state;
  return true;
}

// §20.7 with §7.4.2 and §8.5: describes into `class_array` the unpacked
// dimensions of the property with more than one that `arg0` names -- bare
// in a method of the object, where no local shadows it, or through a handle
// -- answering whether it names one.
static bool DescribeMultiDimProperty(const Expr* arg0, SimContext& ctx,
                                     Arena& arena, ArrayInfo& class_array) {
  const ClassObject* obj = nullptr;
  std::string_view name;
  if (arg0->kind == ExprKind::kIdentifier) {
    if (ctx.FindLocalVariable(arg0->text) != nullptr) return false;
    obj = ctx.CurrentThis();
    name = arg0->text;
  } else if (arg0->kind == ExprKind::kMemberAccess &&
             !arg0->is_scope_resolution && arg0->rhs != nullptr) {
    obj = HandleSideObject(arg0->lhs, ctx, arena);
    name = arg0->rhs->text;
  }
  const auto* prop = obj != nullptr ? obj->type->FindProperty(name) : nullptr;
  if (prop == nullptr || prop->dim_sizes.size() < 2) return false;
  class_array.dim_los = prop->dim_los;
  class_array.dim_sizes = prop->dim_sizes;
  class_array.lo = prop->dim_los[0];
  class_array.size = prop->dim_sizes[0];
  class_array.elem_width = prop->width;
  class_array.is_4state = prop->is_4state;
  return true;
}

// §20.7 with §7.2 and §7.4.2: describes into `class_array` the unpacked array
// member of a structure `arg0` names, `m.v`, `r.v` bare in a method or
// `h.r.v`, from the structure's layout, answering whether it names one.
static bool DescribeStructArrayMember(const Expr* arg0, SimContext& ctx,
                                      ArrayInfo& class_array) {
  const StructFieldInfo* field = ResolveStructArrayMember(arg0, ctx);
  if (field == nullptr || field->elem_count == 0) return false;
  class_array.lo = static_cast<uint32_t>(field->elem_left < field->elem_right
                                             ? field->elem_left
                                             : field->elem_right);
  class_array.size = field->elem_count;
  class_array.elem_width = field->width / field->elem_count;
  class_array.is_descending = field->elem_left > field->elem_right;
  return true;
}

// The container `arg0` names where no declared array answers its name: a
// queue property, bare in a method or `h.q` through a handle, the queue its
// object holds (§7.10 with §8.5); a fixed, dynamic or multidimensional array
// property; or a structure's unpacked array member -- the last three
// described into `class_array`.
static void ClassifyUnnamedArray(const Expr* arg0, SimContext& ctx,
                                 Arena& arena, QueryArgInfo& info,
                                 ArrayInfo& class_array) {
  info.queue = FindQueueOfBase(arg0, ctx, arena);
  if (info.queue != nullptr) return;
  if (DescribeClassArray(arg0, ctx, arena, class_array) ||
      DescribeMultiDimProperty(arg0, ctx, arena, class_array) ||
      DescribeStructArrayMember(arg0, ctx, class_array)) {
    info.arr = &class_array;
  }
}

// Resolve the first argument to an unpacked container (if any) and determine
// the width/kind of its packed element dimension. §20.7: a string is a nonarray
// type equivalent to a simple bit vector (one packed dimension); a real type
// contributes no packed dimension.
//
// §20.7 with §8.5: an unpacked array property of a class object, named bare in
// one of its methods or through a handle, is an array too, a queue one
// included, and so is an unpacked array member of a structure. A fixed or
// dynamic one's dimension, a multidimensional one's dimensions, or the
// member's, are described into `class_array`, which the caller keeps for as
// long as it reads the result.
static QueryArgInfo ClassifyQueryArg(const Expr* arg0, SimContext& ctx,
                                     Arena& arena, ArrayInfo& class_array) {
  QueryArgInfo info;
  if (std::string name = QueryArgName(arg0); !name.empty()) {
    info.assoc = ctx.FindAssocArray(name);
    info.queue = ctx.FindQueue(name);
    info.arr = ctx.FindArrayInfo(name);
  }
  bool found =
      info.assoc != nullptr || info.queue != nullptr || info.arr != nullptr;
  if (!found && arg0 != nullptr)
    ClassifyUnnamedArray(arg0, ctx, arena, info, class_array);
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
  // §20.7: each function returns an integer, which is signed, so the -1 of
  // $increment for an ascending dimension reads -1 and not 4294967295.
  auto as_int = [&](int64_t v) {
    Logic4Vec out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(v));
    out.is_signed = true;
    return out;
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
  ArrayInfo class_array;
  QueryArgInfo info = ClassifyQueryArg(arg0, ctx, arena, class_array);

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

// The element count of the unpacked dimension `dim`, `[36:1]` or `[3]`; 0
// for a dynamic one or one of no positive size.
static int64_t FixedDimCount(const Expr* dim, SimContext& ctx, Arena& arena) {
  if (dim == nullptr) return 0;
  auto bound = [&](const Expr* e) {
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return bound(dim);
  int64_t left = bound(dim->lhs);
  int64_t right = bound(dim->rhs);
  return (left > right ? left - right : right - left) + 1;
}

uint64_t TypedefBits(std::string_view name, SimContext& ctx, Arena& arena,
                     int depth) {
  const ModuleItem* item = ctx.FindTypedefItem(name);
  if (item == nullptr || item->unpacked_dims.empty() || depth > 8)
    return ctx.FindTypeWidth(name);
  const DataType& elem = item->typedef_type;
  uint64_t bits = elem.kind == DataTypeKind::kNamed && elem.scope_name.empty()
                      ? TypedefBits(elem.type_name, ctx, arena, depth + 1)
                      : DeclaredTypeWidth(elem, ctx);
  for (const Expr* dim : item->unpacked_dims) {
    int64_t count = FixedDimCount(dim, ctx, arena);
    if (count <= 0) return 0;
    bits *= static_cast<uint64_t>(count);
  }
  return bits;
}

}  // namespace delta
