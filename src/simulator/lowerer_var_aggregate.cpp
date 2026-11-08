#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_element_shape.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static void RecordAssocElemInit(std::string_view name, const RtlirVariable& var,
                                AssocArrayObject* aa, SimContext& ctx,
                                Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  bool any_init = false;
  for (const auto& m : var.dtype->struct_members) {
    if (m.init_expr) any_init = true;
  }
  if (!any_init) return;
  auto* elem = ctx.FindVariable(name);
  if (!elem) return;
  aa->has_elem_init = true;
  aa->elem_init = OwnRhsWords(elem->value, arena);
}

static std::vector<FixedDimShape> InnerDimsOf(const RtlirElementShape& shape) {
  std::vector<FixedDimShape> dims;
  dims.reserve(shape.inner_array_dims.size());
  for (const RtlirFixedDim& dim : shape.inner_array_dims)
    dims.push_back(FixedDimShape{dim.size, dim.lo, dim.descending});
  return dims;
}

static void ApplyElementShape(QueueObject* q,
                              const RtlirElementShape& element) {
  q->nested_queue_levels = element.nested_queue_levels;
  q->element_array_size = element.array_size;
  q->element_array_lo = element.array_lo;
  q->element_array_descending = element.array_descending;
  q->element_inner_dims = InnerDimsOf(element);
}

static void CreateFixedElementQueues(std::string_view name,
                                     const RtlirVariable& var, SimContext& ctx,
                                     Arena& arena) {
  ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr) return;
  info->elements_are_queues = true;
  for (uint32_t i = 0; i < info->size; ++i) {
    auto* key = arena.Create<std::string>(std::string(name) + "[" +
                                          std::to_string(info->lo + i) + "]");
    QueueObject* q = ctx.CreateQueue(*key, var.width, -1, var.is_4state);
    q->is_signed = var.is_signed;
    q->holds_class_handles = !var.class_type_name.empty();
    if (var.element.array_size > 0) {
      q->elements_are_queues = true;
      ApplyElementShape(q, var.element);
      continue;
    }
    q->elements_are_queues = var.element.nested_queue_levels > 0;
    q->nested_queue_levels = var.element.nested_queue_levels > 0
                                 ? var.element.nested_queue_levels - 1
                                 : 0;
  }
}

static const AssocArrayObject* ElementAssocTemplate(
    const AssocArrayObject* outer, const RtlirAssocIndex& index, Arena& arena) {
  auto* inner = arena.Create<AssocArrayObject>();
  inner->elem_width = outer->elem_width;
  inner->is_4state = outer->is_4state;
  inner->is_signed = outer->is_signed;
  inner->is_string_key = index.is_string;
  inner->is_wildcard = index.is_wildcard;
  inner->is_index_signed = index.is_signed;
  inner->index_width = index.width;
  inner->index_class = index.class_name;
  inner->index_type_name = index.type_name;
  return inner;
}

static void InitFixedArrayFromConcat(std::string_view name,
                                     const RtlirVariable& var, SimContext& ctx,
                                     Arena& arena) {
  if (var.unpacked_size == 0 || var.init_expr == nullptr ||
      var.init_expr->kind != ExprKind::kConcatenation) {
    return;
  }
  DistributeConcatToArray(name, *ctx.FindArrayInfo(name), var.init_expr, ctx,
                          arena);
}

void Lowerer::LowerVarAggregate(std::string_view name,
                                const RtlirVariable& var) {
  if (var.is_queue) {
    auto* q = ctx_.CreateQueue(name, var.is_event ? 64 : var.width,
                               var.queue_max_size, var.is_4state);
    q->is_signed = var.is_signed;
    q->elem_type_kind = var.elem_type_kind;
    q->holds_events = var.is_event;
    q->holds_class_handles = !var.class_type_name.empty();
    q->elements_are_queues = var.elements_are_queues;
    ApplyElementShape(q, var.element);
    LowerDynArrayInit(q, var);
  } else if (var.is_dynamic) {
    auto* q = ctx_.CreateQueue(name, var.width, -1, var.is_4state);
    q->is_signed = var.is_signed;
    q->elem_type_kind = var.elem_type_kind;
    q->elements_are_queues = var.elements_are_queues;
    ApplyElementShape(q, var.element);
    LowerDynArrayInit(q, var);

    ArrayInfo info;
    info.is_dynamic = true;
    info.elem_width = var.width;
    info.is_4state = var.is_4state;
    ctx_.RegisterArray(name, info);
  } else if (var.is_assoc) {
    auto* aa = ctx_.CreateAssocArray(
        name, var.width, var.is_string_index,
        AssocArraySpec{var.assoc_index_width, var.is_wildcard_index,
                       var.is_4state, var.is_index_signed,
                       var.assoc_index_class_name, var.assoc_index_type_name});
    aa->is_signed = var.is_signed;
    aa->elements_are_queues = var.elements_are_queues;
    aa->nested_queue_levels = var.element.nested_queue_levels;
    aa->element_array_size = var.element.array_size;
    aa->element_array_lo = var.element.array_lo;
    aa->element_array_descending = var.element.array_descending;
    aa->element_inner_dims = InnerDimsOf(var.element);
    if (var.element.assoc_index) {
      aa->element_assoc =
          ElementAssocTemplate(aa, *var.element.assoc_index, arena_);
    }
    aa->element_queue_handles =
        var.elements_are_queues && !var.class_type_name.empty();
    InitAssocDefault(var.init_expr, aa);
    RecordAssocElemInit(name, var, aa, ctx_, arena_);
  } else {
    CreateArrayElements(name, var, ctx_, arena_);
    InitFixedArrayFromConcat(name, var, ctx_, arena_);
    if (var.elements_are_queues)
      CreateFixedElementQueues(name, var, ctx_, arena_);
  }
}

}  // namespace delta
