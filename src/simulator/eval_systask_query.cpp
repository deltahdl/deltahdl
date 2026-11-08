#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/assoc_index.h"
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
#include "simulator/virtual_interface.h"

namespace delta {

static Logic4Vec MakeUnknownInt(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  uint64_t mask = (width < 64) ? ((uint64_t{1} << width) - 1) : ~uint64_t{0};
  if (vec.nwords > 0) {
    vec.words[0].aval = mask;
    vec.words[0].bval = mask;
  }
  return vec;
}

struct QueryDimBounds {
  int64_t left = 0;
  int64_t right = 0;
  int64_t low = 0;
  int64_t high = 0;
  int64_t increment = 1;
  int64_t size = 0;
  bool low_high_unknown = false;
};

struct QueryArgInfo {
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  const ArrayInfo* arr = nullptr;
  bool dynamic_outer = false;
  bool has_unpacked = false;
  uint32_t elem_width = 32;
  bool is_real = false;
  bool is_string = false;
  std::vector<PackedRange> packed_dims;
  QueueObject* element_queue = nullptr;
};

std::string ArrayArgPath(const Expr* arg0, SimContext& ctx, Arena& arena) {
  if (arg0 == nullptr) return {};
  if (arg0->kind == ExprKind::kIdentifier) return std::string(arg0->text);
  if (arg0->kind != ExprKind::kMemberAccess || arg0->is_scope_resolution) {
    return {};
  }
  if (arg0->lhs != nullptr && arg0->rhs != nullptr) {
    VirtualInterfaceBase vi =
        ResolveVirtualInterfaceBaseExpr(arg0->lhs, ctx, arena);
    if (vi.is_virtual_interface && vi.handle != kNullVirtualInterface) {
      return VirtualInterfaceComponentName(vi.handle, arg0->rhs->text, ctx);
    }
  }
  return FlattenHierPath(arg0);
}

static bool DescribeClassArray(const Expr* arg0, SimContext& ctx, Arena& arena,
                               ArrayInfo& class_array) {
  ClassArrayRef ref;
  if (arg0 == nullptr || !ResolveClassArray(arg0, ctx, arena, ref)) {
    return false;
  }
  if (ref.dim == 0 && ref.prop->dim_sizes.size() >= 2) return false;
  class_array.lo = static_cast<uint32_t>(ref.lo);
  class_array.size = ref.size;
  class_array.elem_width = ref.prop->width;
  class_array.is_descending = ref.prop->array_descending;
  class_array.is_dynamic = ref.prop->is_dynamic;
  class_array.is_4state = ref.prop->is_4state;
  return true;
}

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

static std::vector<PackedRange> PackedDimsOf(const Expr* arg0, Arena& arena,
                                             const QueryArgInfo& info,
                                             SimContext& ctx) {
  std::string name = ArrayArgPath(arg0, ctx, arena);
  if (name.empty() || info.assoc != nullptr || info.queue != nullptr) return {};
  const Variable* v = ctx.FindVariable(name);
  if ((v == nullptr || !v->has_packed_range) && info.arr != nullptr &&
      info.arr->dim_sizes.empty()) {
    v = ctx.FindVariable(name + "[" + std::to_string(info.arr->lo) + "]");
  }
  if (v == nullptr || !v->has_packed_range) return {};
  std::vector<PackedRange> dims{v->packed_range};
  dims.insert(dims.end(), v->inner_packed_dims.begin(),
              v->inner_packed_dims.end());
  return dims;
}

static uint32_t IntegralKeywordBits(std::string_view name) {
  if (name == "bit" || name == "logic" || name == "reg") return 1;
  if (name == "byte") return 8;
  if (name == "shortint") return 16;
  if (name == "int" || name == "integer") return 32;
  if (name == "longint" || name == "time") return 64;
  return 0;
}

static std::vector<PackedRange> TypeNameDims(std::string_view name,
                                             SimContext& ctx, Arena& arena) {
  if (uint32_t bits = IntegralKeywordBits(name); bits > 0) {
    return {PackedRange{static_cast<int64_t>(bits) - 1, 0}};
  }
  const DataType* type = ctx.FindTypeDeclaration(name);
  for (int hops = 0; type != nullptr && hops < 16; ++hops) {
    std::vector<PackedRange> dims;
    auto bound = [&](const Expr* e) {
      return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
    };
    if (type->packed_dim_left != nullptr && type->packed_dim_right != nullptr) {
      dims.push_back(
          {bound(type->packed_dim_left), bound(type->packed_dim_right)});
    }
    for (const auto& [left, right] : type->extra_packed_dims) {
      dims.push_back({bound(left), bound(right)});
    }
    if (!dims.empty()) return dims;
    if (type->kind != DataTypeKind::kNamed) {
      uint32_t width = DeclaredTypeWidth(*type, ctx);
      if (width == 0) return {};
      return {PackedRange{static_cast<int64_t>(width) - 1, 0}};
    }
    type = ctx.FindTypeDeclaration(type->type_name);
  }
  return {};
}

static void DescribeElement(const Expr* arg0, SimContext& ctx, Arena& arena,
                            QueryArgInfo& info) {
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
}

static QueryArgInfo ClassifyQueryArg(const Expr* arg0, SimContext& ctx,
                                     Arena& arena, ArrayInfo& class_array) {
  QueryArgInfo info;
  if (std::string name = ArrayArgPath(arg0, ctx, arena); !name.empty()) {
    info.assoc = ctx.FindAssocArray(name);
    info.queue = ctx.FindQueue(name);
    info.arr = ctx.FindArrayInfo(name);
    if (info.arr != nullptr && info.arr->elements_are_queues) {
      info.element_queue =
          ctx.FindQueue(name + "[" + std::to_string(info.arr->lo) + "]");
    }
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

  info.packed_dims = PackedDimsOf(arg0, arena, info, ctx);
  if (!info.has_unpacked && arg0 != nullptr &&
      arg0->kind == ExprKind::kIdentifier &&
      ctx.FindVariable(arg0->text) == nullptr) {
    info.packed_dims = TypeNameDims(arg0->text, ctx, arena);
    if (!info.packed_dims.empty()) return info;
  }
  DescribeElement(arg0, ctx, arena, info);
  return info;
}

static QueryDimBounds AssocDimBounds(AssocArrayObject* assoc) {
  QueryDimBounds q;
  uint32_t iw = assoc->index_width ? assoc->index_width : 32;
  uint32_t value_bits = assoc->is_index_signed ? iw - 1 : iw;
  q.left = 0;
  q.right = (value_bits >= 64)
                ? static_cast<int64_t>(~uint64_t{0})
                : static_cast<int64_t>((uint64_t{1} << value_bits) - 1);
  q.increment = -1;
  q.size = assoc->Size();
  if (assoc->int_data.empty()) {
    q.low_high_unknown = true;
  } else {
    q.low = assoc->int_data.begin()->first.Low();
    q.high = assoc->int_data.rbegin()->first.Low();
  }
  return q;
}

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

static QueryDimBounds DynamicDimBounds(const QueryArgInfo& info) {
  if (info.queue != nullptr &&
      (info.queue->index_lo != 0 || info.queue->index_descending)) {
    ArrayInfo element;
    element.size = static_cast<uint32_t>(info.queue->elements.size());
    element.lo = static_cast<uint32_t>(info.queue->index_lo);
    element.is_descending = info.queue->index_descending;
    return FixedUnpackedDimBounds(&element);
  }
  QueryDimBounds q;
  int64_t count = info.queue
                      ? static_cast<int64_t>(info.queue->elements.size())
                      : static_cast<int64_t>(info.arr ? info.arr->size : 0);
  q.left = 0;
  q.right = count - 1;
  q.low = 0;
  q.high = count - 1;
  q.increment = -1;
  q.size = count;
  return q;
}

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

static QueryDimBounds PackedDimBounds(const PackedRange& range) {
  QueryDimBounds q;
  q.left = range.left;
  q.right = range.right;
  q.low = range.LowIndex();
  q.high = range.HighIndex();
  q.size = q.high - q.low + 1;
  q.increment = (q.left >= q.right) ? 1 : -1;
  return q;
}

static uint32_t QueueDimCount(const QueueObject* q) {
  if (q->element_array_size > 0)
    return 2 + static_cast<uint32_t>(q->element_inner_dims.size());
  return q->elements_are_queues ? 2 + q->nested_queue_levels : 1;
}

static uint32_t UnpackedDimCount(const QueryArgInfo& info) {
  if (info.element_queue != nullptr)
    return 1 + QueueDimCount(info.element_queue);
  if (info.arr && info.arr->dim_sizes.size() >= 2)
    return static_cast<uint32_t>(info.arr->dim_sizes.size());
  if (info.queue != nullptr) return QueueDimCount(info.queue);
  return info.has_unpacked ? 1 : 0;
}

static QueryDimBounds ElementArrayDimBounds(const QueueObject* q) {
  ArrayInfo element;
  element.size = q->element_array_size;
  element.lo = static_cast<uint32_t>(q->element_array_lo);
  element.is_descending = q->element_array_descending;
  return FixedUnpackedDimBounds(&element);
}

static std::vector<QueryDimBounds> QueueShapeDims(QueueObject* q) {
  QueryArgInfo queue;
  queue.queue = q;
  std::vector<QueryDimBounds> dims = {DynamicDimBounds(queue),
                                      ElementArrayDimBounds(q)};
  for (const FixedDimShape& inner : q->element_inner_dims) {
    ArrayInfo shape;
    shape.size = inner.size;
    shape.lo = static_cast<uint32_t>(inner.lo);
    shape.is_descending = inner.descending;
    dims.push_back(FixedUnpackedDimBounds(&shape));
  }
  return dims;
}

static QueryDimBounds DimOf(const std::vector<QueryDimBounds>& dims,
                            uint32_t dim) {
  return dims[std::min<size_t>(dim - 1, dims.size() - 1)];
}

static QueryDimBounds ElementQueueShapeDimBounds(const QueryArgInfo& info,
                                                 uint32_t dim) {
  std::vector<QueryDimBounds> dims = QueueShapeDims(info.element_queue);
  dims.insert(dims.begin(), FixedUnpackedDimBounds(info.arr));
  return DimOf(dims, dim);
}

static QueryDimBounds UnpackedQueryDimBounds(const QueryArgInfo& info,
                                             uint32_t dim) {
  if (info.element_queue != nullptr)
    return ElementQueueShapeDimBounds(info, dim);
  if (info.queue != nullptr) return DimOf(QueueShapeDims(info.queue), dim);
  if (info.assoc) return AssocDimBounds(info.assoc);
  if (info.dynamic_outer) return DynamicDimBounds(info);
  if (info.arr->dim_sizes.size() >= 2)
    return MultiDimUnpackedDimBounds(info.arr, dim);
  return FixedUnpackedDimBounds(info.arr);
}

static QueryDimBounds ComputeQueryDimBounds(const QueryArgInfo& info,
                                            uint32_t dim,
                                            uint32_t unpacked_dims) {
  if (dim <= unpacked_dims) return UnpackedQueryDimBounds(info, dim);
  if (!info.packed_dims.empty()) {
    return PackedDimBounds(info.packed_dims[std::min<size_t>(
        dim - unpacked_dims - 1, info.packed_dims.size() - 1)]);
  }
  return PackedElemDimBounds(info.elem_width);
}

static uint32_t CountTotalDims(const QueryArgInfo& info,
                               uint32_t& unpacked_dims) {
  uint32_t packed_dims =
      (info.is_string || (info.elem_width > 0 && !info.is_real)) ? 1 : 0;
  if (!info.packed_dims.empty())
    packed_dims = static_cast<uint32_t>(info.packed_dims.size());
  unpacked_dims = UnpackedDimCount(info);
  return packed_dims + unpacked_dims;
}

static Logic4Vec SelectDimQueryResult(std::string_view name,
                                      const QueryDimBounds& q, Arena& arena) {
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
  return as_int(q.size);
}

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  const Expr* arg0 = expr->args.empty() ? nullptr : expr->args[0];

  ArrayInfo class_array;
  QueryArgInfo info = ClassifyQueryArg(arg0, ctx, arena, class_array);

  uint32_t unpacked_dims = 0;
  uint32_t total_dims = CountTotalDims(info, unpacked_dims);

  if (name == "$dimensions") return MakeLogic4VecVal(arena, 32, total_dims);
  if (name == "$unpacked_dimensions")
    return MakeLogic4VecVal(arena, 32, unpacked_dims);

  if (total_dims == 0) return MakeUnknownInt(arena, 32);
  uint32_t dim = 1;
  if (expr->args.size() > 1)
    dim = static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  if (dim < 1 || dim > total_dims) return MakeUnknownInt(arena, 32);

  QueryDimBounds q = ComputeQueryDimBounds(info, dim, unpacked_dims);
  return SelectDimQueryResult(name, q, arena);
}

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
  if (uint32_t bits = IntegralKeywordBits(name); bits > 0) return bits;
  const ModuleItem* item = ctx.FindTypedefItem(name);
  if (item == nullptr || item->unpacked_dims.empty() || depth > 8) {
    uint32_t width =
        item != nullptr ? DeclaredTypeWidth(item->typedef_type, ctx) : 0;
    return width > 0 ? width : ctx.FindTypeWidth(name);
  }
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
