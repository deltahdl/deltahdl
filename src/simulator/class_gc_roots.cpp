#include "simulator/class_gc_roots.h"

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// The 64 bits of `value` from bit `at` up, zero past its last word.
uint64_t WindowAt(const Logic4Vec& value, uint32_t at) {
  const uint32_t kWord = at / 64;
  const uint32_t kShift = at % 64;
  if (kWord >= value.nwords) return 0;
  uint64_t window = value.words[kWord].aval >> kShift;
  if (kShift != 0 && kWord + 1 < value.nwords) {
    window |= value.words[kWord + 1].aval << (64 - kShift);
  }
  return window;
}

}  // namespace

ClassGcMarker::ClassGcMarker(
    const std::unordered_map<uint64_t, ClassObject*>& objects,
    std::unordered_set<uint64_t>& live)
    : objects_(objects), live_(live) {}

void ClassGcMarker::Handle(uint64_t handle) {
  if (handle == kNullClassHandle || !objects_.contains(handle)) return;
  if (live_.insert(handle).second) pending_.push_back(handle);
}

void ClassGcMarker::Words(const Logic4Vec& value) {
  for (uint32_t i = 0; i < value.nwords; ++i) Handle(value.words[i].aval);
}

void ClassGcMarker::Fields(const Logic4Vec& value, const StructTypeInfo& layout,
                           uint32_t base) {
  // §7.2: a member of an unpacked structure sits at whatever bit its layout
  // puts it, which a reading of whole words misses unless it starts one, so a
  // member of a class type is read where it stands, and a nested structure
  // member at the bits its own layout gives within it.
  for (const StructFieldInfo& field : layout.fields) {
    const uint32_t kAt = base + field.bit_offset;
    if (field.nested != nullptr) {
      Fields(value, *field.nested, kAt);
    } else if (field.type_kind == DataTypeKind::kNamed) {
      Handle(WindowAt(value, kAt));
    }
  }
}

void ClassGcMarker::Var(const Variable* var) {
  if (var == nullptr) return;
  Words(var->value);
  // §8.29: a pending nonblocking assignment to the variable keeps what it will
  // write reachable.
  if (var->has_pending_nba) Words(var->pending_nba);
}

void ClassGcMarker::Queue(const QueueObject* queue) {
  if (queue == nullptr) return;
  for (const Logic4Vec& element : queue->elements) Words(element);
  for (const auto& [key, nested] : queue->element_queues) Queue(nested);
}

void ClassGcMarker::Assoc(const AssocArrayObject* assoc) {
  if (assoc == nullptr) return;
  // §7.8.5: an array indexed by a class keeps the objects of its keys as well
  // as those its elements hold.
  for (const auto& [key, element] : assoc->int_data) {
    Handle(static_cast<uint64_t>(key.Low()));
    Words(element);
  }
  for (const auto& [key, element] : assoc->str_data) Words(element);
  Words(assoc->default_value);
  for (const auto& [key, nested] : assoc->int_element_queues) Queue(nested);
  for (const auto& [key, nested] : assoc->str_element_queues) Queue(nested);
  for (const auto& [key, nested] : assoc->int_element_assocs) Assoc(nested);
  for (const auto& [key, nested] : assoc->str_element_assocs) Assoc(nested);
}

void ClassGcMarker::Mailbox(const MailboxObject* mailbox) {
  if (mailbox == nullptr) return;
  for (const Logic4Snapshot& message : mailbox->messages) Words(message.Get());
}

void ClassGcMarker::InScope(const Scope& scope) {
  for (const auto& [name, var] : scope.vars) Var(var);
  for (const auto& [name, queue] : scope.queues) Queue(queue);
  for (const auto& [name, assoc] : scope.assoc_arrays) Assoc(assoc);
}

void ClassGcMarker::Stacks(const Process& proc) {
  if (proc.sv_state == ProcessState::kFinished ||
      proc.sv_state == ProcessState::kKilled) {
    return;
  }
  for (const Scope& scope : proc.saved_scope_stack) InScope(scope);
  for (const ClassObject* obj : proc.saved_this_stack) {
    if (obj != nullptr) Handle(obj->handle);
  }
}

void ClassGcMarker::Statics(const ClassTypeInfo& type) {
  for (const auto& [name, value] : type.static_properties) Words(value);
  for (const auto& [name, queue] : type.static_queue_properties) Queue(queue);
  for (const auto& [name, assoc] : type.static_assoc_properties) Assoc(assoc);
  for (const auto& [name, mailbox] : type.static_mailbox_properties) {
    Mailbox(mailbox);
  }
}

void ClassGcMarker::Object(const ClassObject& obj) {
  for (const auto& [name, value] : obj.properties) Words(value);
  for (const auto& [name, queue] : obj.queue_properties) Queue(queue);
  for (const auto& [name, assoc] : obj.assoc_properties) Assoc(assoc);
  for (const auto& [name, mailbox] : obj.mailbox_properties) Mailbox(mailbox);
  for (const auto& [name, cell] : obj.ref_cells) Var(cell.var);
}

void ClassGcMarker::Propagate() {
  while (!pending_.empty()) {
    const uint64_t kHandle = pending_.back();
    pending_.pop_back();
    Object(*objects_.at(kHandle));
  }
}

namespace {

// The handles among the words of `value` that name class objects, added to
// `handles`.
void AddObjectHandles(SimContext& ctx, const Logic4Vec& value,
                      std::vector<uint64_t>& handles) {
  for (uint32_t i = 0; i < value.nwords; ++i) {
    if (ctx.GetClassObject(value.words[i].aval) != nullptr) {
      handles.push_back(value.words[i].aval);
    }
  }
}

// A pin holding `handles` in the scheduler's pinned set until it is released;
// null where there are none.
std::shared_ptr<void> PinHandles(Scheduler& scheduler,
                                 std::vector<uint64_t> handles) {
  if (handles.empty()) return nullptr;
  for (uint64_t handle : handles) scheduler.PinHandle(handle);
  return {nullptr, [&scheduler, handles = std::move(handles)](void*) {
            for (uint64_t handle : handles) scheduler.UnpinHandle(handle);
          }};
}

}  // namespace

std::shared_ptr<void> PinClassHandles(SimContext& ctx, const Logic4Vec& value) {
  std::vector<uint64_t> handles;
  AddObjectHandles(ctx, value, handles);
  return PinHandles(ctx.GetScheduler(), std::move(handles));
}

PinnedValue PinValue(SimContext& ctx, const Logic4Vec& value) {
  return {value, PinClassHandles(ctx, value)};
}

void PinEventHandles(Event& event, SimContext& ctx,
                     const std::vector<Logic4Vec>& values,
                     const ClassObject* target) {
  std::vector<uint64_t> handles;
  for (const Logic4Vec& value : values) AddObjectHandles(ctx, value, handles);
  if (target != nullptr) handles.push_back(target->handle);
  // A pin owns no pointer, only the deleter that unpins its handles, so it is
  // the handles and not the pin that say whether there is anything to keep.
  if (handles.empty()) return;
  std::shared_ptr<void> pin =
      PinHandles(ctx.GetScheduler(), std::move(handles));
  event.callback = [pin, run = std::move(event.callback)]() { run(); };
}

}  // namespace delta
