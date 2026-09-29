#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_element_shape.h"
#include "parser/ast_type.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §7.8.7: an element allocated by a write starts at the initial value its
// type gives it, which for a struct is its members' initializers rather than
// zero. LowerVar has already deposited those onto the variable it created
// under this name, which models one element of the array, so the pattern is
// read back from there rather than evaluated a second time.
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
  // The element model is a live Variable, so the initial value the array keeps
  // takes its own words rather than the variable's: an entry allocated from
  // elem_init is §6.8 storage of its own (see AssocAllocValue), and a stored
  // initial value that shares with a variable would be one more name for the
  // same buffer behind them all.
  aa->elem_init = OwnRhsWords(elem->value, arena);
}

// §7.4 with §7.10: each element of a fixed-size array whose elements are
// queues, `q_t fx[2]` under `typedef int q_t[$];`, is a queue, created under
// the element's own name, `fx[1]`, where ElementQueueOfSelect
// (eval_array_element_queue.h) finds it, and the array's shape says so. With
// no queue there, `fx[1].push_back(4)` found nothing to push onto.
static void CreateFixedElementQueues(std::string_view name,
                                     const RtlirVariable& var, SimContext& ctx,
                                     Arena& arena) {
  ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr) return;
  info->elements_are_queues = true;
  for (uint32_t i = 0; i < info->size; ++i) {
    auto* key = arena.Create<std::string>(std::string(name) + "[" +
                                          std::to_string(info->lo + i) + "]");
    QueueObject* q =
        ctx.CreateQueue(*key, var.width, /*max_size=*/-1, var.is_4state);
    q->is_signed = var.is_signed;
    q->holds_class_handles = !var.class_type_name.empty();
    // §7.4 with §7.5: in `int arr[2][][]` the element's queue, arr[0], holds
    // queues itself.
    q->elements_are_queues = var.element.nested_queue_levels > 0;
    q->nested_queue_levels = var.element.nested_queue_levels > 0
                                 ? var.element.nested_queue_levels - 1
                                 : 0;
  }
}

// §7.8 with §7.4 (printed pages 162 and 153): the empty array each element
// of `outer`, an associative array whose element type is an associative array
// indexed by `index`, starts as: of the elements `outer` declares, under that
// index.
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

// §7.4.4: the dimensions of a multidimensional element after its first, as
// the element queues below each level are made with.
static std::vector<FixedDimShape> InnerDimsOf(const RtlirElementShape& shape) {
  std::vector<FixedDimShape> dims;
  dims.reserve(shape.inner_array_dims.size());
  for (const RtlirFixedDim& dim : shape.inner_array_dims)
    dims.push_back(FixedDimShape{dim.size, dim.lo, dim.descending});
  return dims;
}

void Lowerer::LowerVarAggregate(std::string_view name,
                                const RtlirVariable& var) {
  if (var.is_queue) {
    auto* q =
        ctx_.CreateQueue(name, var.width, var.queue_max_size, var.is_4state);
    q->is_signed = var.is_signed;
    // §8.4: a queue of a class type holds handles, so `q[i].v` names a
    // property of the object an element refers to (TryEvalQueueElementMember
    // in eval_array_class_queue.h).
    q->holds_class_handles = !var.class_type_name.empty();
    q->elements_are_queues = var.elements_are_queues;
    q->nested_queue_levels = var.element.nested_queue_levels;
    q->element_array_size = var.element.array_size;
    q->element_array_lo = var.element.array_lo;
    q->element_array_descending = var.element.array_descending;
    q->element_inner_dims = InnerDimsOf(var.element);
    // §7.10.1: a queue may be initialized from an assignment-pattern literal
    // (e.g. int q[$] = '{10, 20, 30}). Populate its elements like a dynamic
    // array; LowerDynArrayInit is a no-op when there is no initializer.
    LowerDynArrayInit(q, var);
  } else if (var.is_dynamic) {
    // Carry the element's state-ness onto the backing store: §21.4.2 keys the
    // x/z-to-0 memory-load coercion on it, and it governs 2-state defaults.
    auto* q = ctx_.CreateQueue(name, var.width, /*max_size=*/-1, var.is_4state);
    q->is_signed = var.is_signed;
    q->elements_are_queues = var.elements_are_queues;
    q->nested_queue_levels = var.element.nested_queue_levels;
    q->element_array_size = var.element.array_size;
    q->element_array_lo = var.element.array_lo;
    q->element_array_descending = var.element.array_descending;
    q->element_inner_dims = InnerDimsOf(var.element);
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
    // §7.8 with §7.10: an array whose elements are queues keeps a queue under
    // each key (eval_array_element_queue.h), handles where the element type
    // is a class.
    aa->elements_are_queues = var.elements_are_queues;
    aa->nested_queue_levels = var.element.nested_queue_levels;
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
    if (var.elements_are_queues)
      CreateFixedElementQueues(name, var, ctx_, arena_);
  }
}

}  // namespace delta
