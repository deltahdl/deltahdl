#include <gtest/gtest.h>

#include <cstdint>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/assoc_index.h"
#include "simulator/class_gc_roots.h"
#include "simulator/class_object.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/scope.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §8.29: the marking half of the class garbage collector, read off one place a
// run keeps a handle at a time. Each case gives the marker three objects,
// handles 1 to 3, and checks which of them a store it is handed reaches.
class ClassGcMarking : public ::testing::Test {
 protected:
  // A value of `width` bits holding `handle` at bit 0.
  Logic4Vec Holding(uint64_t handle, uint32_t width = 64) {
    Logic4Vec value = MakeLogic4Vec(arena_, width);
    value.words[0].aval = handle;
    return value;
  }

  Arena arena_;
  ClassObject one_, two_, three_;
  std::unordered_map<uint64_t, ClassObject*> objects_{
      {1, &one_}, {2, &two_}, {3, &three_}};
  std::unordered_set<uint64_t> live_;
  ClassGcMarker mark_{objects_, live_};
};

// Nothing a null store, an empty value, the null handle or a handle no object
// has refers to is marked; nor is a window of a wide value above the highest
// handle.
TEST_F(ClassGcMarking, NothingIsMarkedThroughAnEmptyStore) {
  mark_.Var(nullptr);
  mark_.Queue(nullptr);
  mark_.Assoc(nullptr);
  mark_.Mailbox(nullptr);
  mark_.Words(Logic4Vec{});
  mark_.Handle(kNullClassHandle);
  mark_.Handle(9);
  mark_.Words(Holding(9, 96));
  EXPECT_TRUE(live_.empty());
}

// §7.2: a structure's class-typed members are read where its layout puts them
// (#7226): a handle at bit 32, after the int below it, and one in a nested
// structure's member; a member of another type, and one the value is too short
// to hold, are not read as handles.
TEST_F(ClassGcMarking, AStructuresClassMembersAreMarkedWhereTheyStand) {
  StructTypeInfo inner;
  inner.fields.push_back({"n", 0, 64, DataTypeKind::kNamed});
  StructTypeInfo layout;
  layout.fields.push_back({"i", 0, 32, DataTypeKind::kInt});
  layout.fields.push_back({"h", 32, 64, DataTypeKind::kNamed});
  StructFieldInfo nested{"s", 96, 64, DataTypeKind::kStruct};
  nested.nested = &inner;
  layout.fields.push_back(nested);
  layout.fields.push_back({"far", 400, 64, DataTypeKind::kNamed});
  Logic4Vec value = MakeLogic4Vec(arena_, 160);
  value.words[0].aval = (uint64_t{2} << 32) | 3;
  value.words[1].aval = uint64_t{1} << 32;
  mark_.Fields(value, layout);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2}));
}

// A variable's value and the value a pending nonblocking assignment will write
// to it are both roots.
TEST_F(ClassGcMarking, AVariablesValueAndPendingValueAreMarked) {
  Variable var;
  var.value = Holding(1);
  var.pending_nba = Holding(2);
  var.has_pending_nba = true;
  mark_.Var(&var);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2}));
}

// A queue's elements are roots, and so are those of the queues its elements
// are.
TEST_F(ClassGcMarking, AQueuesElementsAndNestedQueuesAreMarked) {
  QueueObject inner;
  inner.elements.push_back(Holding(2));
  QueueObject outer;
  outer.elements.push_back(Holding(1));
  outer.element_queues[0] = &inner;
  mark_.Queue(&outer);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2}));
}

// An associative array's class-handle keys, values, default and nested arrays
// are roots.
TEST_F(ClassGcMarking, AnAssocArraysKeysValuesDefaultAndNestedAreMarked) {
  QueueObject queue;
  queue.elements.push_back(Holding(3));
  AssocArrayObject nested;
  nested.str_data["k"] = Holding(3);
  AssocArrayObject assoc;
  assoc.int_data[AssocIndex(1)] = Holding(kNullClassHandle);
  assoc.str_data["s"] = Holding(2);
  assoc.default_value = Holding(kNullClassHandle);
  assoc.int_element_queues[AssocIndex(0)] = &queue;
  assoc.str_element_queues["q"] = &queue;
  assoc.int_element_assocs[AssocIndex(0)] = &nested;
  assoc.str_element_assocs["a"] = &nested;
  mark_.Assoc(&assoc);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2, 3}));
}

// A mailbox's messages are roots.
TEST_F(ClassGcMarking, AMailboxsMessagesAreMarked) {
  MailboxObject mailbox;
  Logic4Snapshot message;
  message.Capture(Holding(3));
  mailbox.messages.push_back(message);
  mark_.Mailbox(&mailbox);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{3}));
}

// A suspended process's parked scopes and the objects its method calls run on
// are roots; a finished or killed process's are not.
TEST_F(ClassGcMarking, OnlyALiveProcesssStacksAreMarked) {
  Variable var;
  var.value = Holding(1);
  QueueObject queue;
  queue.elements.push_back(Holding(2));
  AssocArrayObject assoc;
  assoc.str_data["s"] = Holding(2);
  Scope scope;
  scope.vars["v"] = &var;
  scope.queues["q"] = &queue;
  scope.assoc_arrays["a"] = &assoc;
  three_.handle = 3;

  Process ended;
  ended.saved_scope_stack.push_back(scope);
  ended.sv_state = ProcessState::kFinished;
  mark_.Stacks(ended);
  ended.sv_state = ProcessState::kKilled;
  mark_.Stacks(ended);
  EXPECT_TRUE(live_.empty());

  Process waiting;
  waiting.saved_scope_stack.push_back(scope);
  waiting.saved_this_stack = {nullptr, &three_};
  mark_.Stacks(waiting);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2, 3}));
}

// A class's static properties are roots, whatever container holds them.
TEST_F(ClassGcMarking, AClasssStaticPropertiesAreMarked) {
  QueueObject queue;
  queue.elements.push_back(Holding(2));
  AssocArrayObject assoc;
  assoc.str_data["s"] = Holding(2);
  MailboxObject mailbox;
  Logic4Snapshot message;
  message.Capture(Holding(3));
  mailbox.messages.push_back(message);
  ClassTypeInfo type;
  type.static_properties["p"] = Holding(1);
  type.static_queue_properties["q"] = &queue;
  type.static_assoc_properties["a"] = &assoc;
  type.static_mailbox_properties["m"] = &mailbox;
  mark_.Statics(type);
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2, 3}));
}

// What a live object refers to through any property, container or ref cell
// is marked in turn.
TEST_F(ClassGcMarking, AnObjectsReferencesArePropagated) {
  QueueObject queue;
  queue.elements.push_back(Holding(2));
  AssocArrayObject assoc;
  MailboxObject mailbox;
  Variable cell;
  cell.value = Holding(3);
  one_.properties["self"] = Holding(1);
  one_.queue_properties["q"] = &queue;
  one_.assoc_properties["a"] = &assoc;
  one_.mailbox_properties["m"] = &mailbox;
  one_.ref_cells["r"].var = &cell;
  mark_.Handle(1);
  mark_.Propagate();
  EXPECT_EQ(live_, (std::unordered_set<uint64_t>{1, 2, 3}));
}

// A handle pinned twice stays pinned until both pins are released; releasing
// one that was never pinned changes nothing.
TEST(ClassGcPins, AHandlePinnedTwiceStaysPinnedUntilBothAreReleased) {
  Arena arena;
  Scheduler scheduler{arena};
  scheduler.PinHandle(4);
  scheduler.PinHandle(4);
  scheduler.UnpinHandle(4);
  EXPECT_TRUE(scheduler.PinnedHandles().contains(4));
  scheduler.UnpinHandle(4);
  scheduler.UnpinHandle(5);
  EXPECT_TRUE(scheduler.PinnedHandles().empty());
}

// The mailboxes held through a handle variable and inside a container are
// both held mailboxes.
TEST(ClassGcHeldMailboxes, HandleAndContainerMailboxesAreHeld) {
  DeclaredNameTables tables;
  MailboxObject by_handle;
  MailboxObject contained;
  Variable var;
  tables.BindMailboxHandle(&var, &by_handle);
  tables.RecordContainedMailbox(&contained);
  EXPECT_EQ(tables.HeldMailboxes().size(), 2u);
}

}  // namespace
