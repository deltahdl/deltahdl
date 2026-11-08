#pragma once

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"

namespace delta {

struct AssocArrayObject;
struct ClassObject;
struct ClassTypeInfo;
struct Event;
struct MailboxObject;
struct Process;
struct QueueObject;
struct Scope;
struct StructTypeInfo;
class SimContext;
struct Variable;

class ClassGcMarker {
 public:
  ClassGcMarker(const std::unordered_map<uint64_t, ClassObject*>& objects,
                std::unordered_set<uint64_t>& live);

  void Handle(uint64_t handle);
  void Words(const Logic4Vec& value);
  void Fields(const Logic4Vec& value, const StructTypeInfo& layout,
              uint32_t base = 0);
  void Var(const Variable* var);
  void Queue(const QueueObject* queue);
  void Assoc(const AssocArrayObject* assoc);
  void Mailbox(const MailboxObject* mailbox);
  void InScope(const Scope& scope);
  void Stacks(const Process& proc);
  void Statics(const ClassTypeInfo& type);
  void Object(const ClassObject& obj);

  void Propagate();

 private:
  const std::unordered_map<uint64_t, ClassObject*>& objects_;
  std::unordered_set<uint64_t>& live_;
  std::vector<uint64_t> pending_;
};

std::shared_ptr<void> PinClassHandles(SimContext& ctx, const Logic4Vec& value);

struct PinnedValue {
  Logic4Vec value;
  std::shared_ptr<void> pin;
};
PinnedValue PinValue(SimContext& ctx, const Logic4Vec& value);

void PinEventHandles(Event& event, SimContext& ctx,
                     const std::vector<Logic4Vec>& values,
                     const ClassObject* target = nullptr);

}  // namespace delta
