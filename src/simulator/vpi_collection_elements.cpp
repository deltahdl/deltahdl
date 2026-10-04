#include "simulator/vpi_collection_elements.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// The stored value an element stands for, or null where its store no longer
// holds one at its index.
Logic4Vec* StoredValue(QueueObject* queue, AssocArrayObject* assoc, int index) {
  if (queue != nullptr) {
    if (index < 0 ||
        static_cast<std::size_t>(index) >= queue->elements.size()) {
      return nullptr;
    }
    return &queue->elements[static_cast<std::size_t>(index)];
  }
  if (assoc != nullptr && !assoc->is_string_key) {
    auto it = assoc->int_data.find(index);
    return it == assoc->int_data.end() ? nullptr : &it->second;
  }
  return nullptr;
}

Logic4Vec* StoredValue(const VpiObject& element) {
  return StoredValue(element.element_of_queue, element.element_of_assoc,
                     element.index);
}

// Copies the words of `from` into `to`, as many as both hold. Logic4Vec
// copies its words pointer rather than its words, so a plain assignment would
// leave the two sharing one store.
void CopyWords(const Logic4Vec& from, Logic4Vec& to) {
  const uint32_t kWords = std::min(from.nwords, to.nwords);
  for (uint32_t i = 0; i < kWords; ++i) to.words[i] = from.words[i];
}

// Copies `width` bits of `from`, starting `from_offset` above its least
// significant end, into `to` from `to_offset` up. Bits past either value's
// width are left alone.
void CopyBits(const Logic4Vec& from, uint32_t from_offset, Logic4Vec& to,
              uint32_t to_offset, uint32_t width) {
  for (uint32_t i = 0; i < width; ++i) {
    const uint32_t kFrom = from_offset + i;
    const uint32_t kTo = to_offset + i;
    if (kFrom / 64 >= from.nwords || kTo / 64 >= to.nwords) return;
    const uint64_t kFromMask = uint64_t{1} << (kFrom % 64);
    const uint64_t kToMask = uint64_t{1} << (kTo % 64);
    const Logic4Word& source = from.words[kFrom / 64];
    Logic4Word& target = to.words[kTo / 64];
    target.aval = (source.aval & kFromMask) != 0 ? target.aval | kToMask
                                                 : target.aval & ~kToMask;
    target.bval = (source.bval & kFromMask) != 0 ? target.bval | kToMask
                                                 : target.bval & ~kToMask;
  }
}

}  // namespace

VpiObject* VpiCollectionElement(VpiObject& array, int index,
                                const VpiAttachBuild& build) {
  Logic4Vec* stored = StoredValue(array.queue, array.assoc, index);
  if (stored == nullptr) return nullptr;
  for (VpiObject* child : array.children) {
    if ((child->element_of_queue != nullptr ||
         child->element_of_assoc != nullptr) &&
        child->index == index) {
      VpiRefreshElementCopy(*child);
      return child;
    }
  }
  VpiObject* element = build.alloc();
  element->type = kVpiReg;
  element->element_of_queue = array.queue;
  element->element_of_assoc = array.assoc;
  element->parent = &array;
  element->array_member = true;
  element->index = index;
  const std::string kSuffix = "[" + std::to_string(index) + "]";
  element->name = build.keep(std::string(array.name) + kSuffix);
  element->full_name = array.full_name + kSuffix;
  auto* storage = build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(build.arena, stored->width);
  storage->value.is_signed = stored->is_signed;
  CopyWords(*stored, storage->value);
  element->var = storage;
  element->size = static_cast<int>(stored->width);
  element->index_expr = VpiIntConstant(index, build);
  element->children.push_back(element->index_expr);
  array.children.push_back(element);
  return element;
}

void VpiRefreshElementCopy(VpiObject& element) {
  if (element.var == nullptr) return;
  const VpiObject* holder = element.member_of;
  if (holder != nullptr && holder->var != nullptr) {
    CopyBits(holder->var->value, element.member_offset, element.var->value, 0,
             element.var->value.width);
    return;
  }
  const Logic4Vec* stored = StoredValue(element);
  if (stored != nullptr) CopyWords(*stored, element.var->value);
}

void VpiStoreElementCopy(VpiObject& element) {
  if (element.var == nullptr) return;
  const VpiObject* holder = element.member_of;
  if (holder != nullptr && holder->var != nullptr) {
    CopyBits(element.var->value, 0, holder->var->value, element.member_offset,
             element.var->value.width);
    return;
  }
  Logic4Vec* stored = StoredValue(element);
  if (stored != nullptr) CopyWords(element.var->value, *stored);
}

}  // namespace delta
