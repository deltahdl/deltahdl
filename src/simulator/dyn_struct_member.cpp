#include "simulator/dyn_struct_member.h"

#include <cstdint>
#include <map>
#include <memory>
#include <tuple>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// Every array of elements a handle names, by handle; handle 0 names none.
std::vector<std::unique_ptr<QueueObject>>& Table() {
  static std::vector<std::unique_ptr<QueueObject>> table(1);
  return table;
}

// An empty array of the elements `field` declares.
std::unique_ptr<QueueObject> EmptyOf(const StructFieldInfo& field) {
  auto queue = std::make_unique<QueueObject>();
  queue->elem_width = field.dyn_elem_width;
  queue->is_4state = Is4stateType(field.type_kind);
  queue->is_signed = field.is_signed;
  return queue;
}

}  // namespace

QueueObject* DynMemberQueue(const Logic4Vec& handle) {
  const auto& table = Table();
  uint64_t index = handle.IsKnown() ? handle.ToUint64() : 0;
  return index < table.size() ? table[index].get() : nullptr;
}

QueueObject* DynMemberEmpty(const StructFieldInfo& field) {
  static std::map<std::tuple<uint32_t, bool, bool>,
                  std::unique_ptr<QueueObject>>
      empties;
  auto& slot = empties[{field.dyn_elem_width, Is4stateType(field.type_kind),
                        field.is_signed}];
  if (slot == nullptr) slot = EmptyOf(field);
  return slot.get();
}

QueueObject* DynMemberForWrite(Logic4Vec& holder, uint32_t offset,
                               const StructFieldInfo& field, Arena& arena) {
  const QueueObject* held =
      DynMemberQueue(ExtractBitField(arena, holder, offset, field.width));
  auto copy =
      held != nullptr ? std::make_unique<QueueObject>(*held) : EmptyOf(field);
  auto& table = Table();
  uint64_t handle = table.size();
  table.push_back(std::move(copy));
  DepositBitField(holder, offset, MakeLogic4VecVal(arena, field.width, handle),
                  field.width);
  return table.back().get();
}

}  // namespace delta
