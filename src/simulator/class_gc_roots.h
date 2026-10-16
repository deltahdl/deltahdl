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
class SimContext;
struct Variable;

// §8.29: the marking half of the class garbage collector. An object is
// strongly reachable while a class handle in any active scope refers to it,
// and a handle can be held in any value the run stores: a variable, an element
// of a queue or an associative array (as a value or a key), a mailbox message,
// a static or instance property, a member of an unpacked struct. The marker
// reads every 64-bit word of each such value and takes one that names an
// object as a reference to it. That is conservative -- an integer equal to an
// object's handle keeps the object -- but never reclaims an object a handle
// still refers to, whatever type the value has.
class ClassGcMarker {
 public:
  ClassGcMarker(const std::unordered_map<uint64_t, ClassObject*>& objects,
                std::unordered_set<uint64_t>& live)
      : objects_(objects), live_(live) {}

  void Handle(uint64_t handle);
  void Words(const Logic4Vec& value);
  void Var(const Variable* var);
  void Queue(const QueueObject* queue);
  void Assoc(const AssocArrayObject* assoc);
  void Mailbox(const MailboxObject* mailbox);
  void InScope(const Scope& scope);
  // The stacks a process parks while suspended, or carries before it first
  // runs; nothing for one that has finished or been killed.
  void Stacks(const Process& proc);
  // The static properties of a class, shared by its objects.
  void Statics(const ClassTypeInfo& type);
  // What an object refers to: its properties, its queue, associative and
  // mailbox properties, and the cells its ref formals write through.
  void Object(const ClassObject& obj);

  // Marks the objects the live ones refer to, and so on, until no more are
  // reached.
  void Propagate();

 private:
  const std::unordered_map<uint64_t, ClassObject*>& objects_;
  std::unordered_set<uint64_t>& live_;
  std::vector<uint64_t> pending_;
};

// §8.29: keeps the class objects `value` refers to reachable for as long as
// the returned pin lives, for a scheduled assignment that carries the value
// until it runs. Null where the value refers to no object.
std::shared_ptr<void> PinClassHandles(SimContext& ctx, const Logic4Vec& value);

// §8.29: a value with the pin keeping what it refers to reachable, for an
// assignment that holds the value across a delay before it writes it.
struct PinnedValue {
  Logic4Vec value;
  std::shared_ptr<void> pin;
};
PinnedValue PinValue(SimContext& ctx, const Logic4Vec& value);

// §8.29: has the scheduled `event` keep what `values` refer to, and the object
// `target` it writes into, reachable until the event is released after it runs.
void PinEventHandles(Event& event, SimContext& ctx,
                     const std::vector<Logic4Vec>& values,
                     const ClassObject* target = nullptr);

}  // namespace delta
