#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.27 named events: the VPI object model for a named event and a named event
// array. The diagram's properties (vpiName/vpiFullName,
// vpiArray/vpiArrayMember, vpiAutomatic, vpiAllocScheme), its
// typespec/value/parent edges, and access by index are owned by the generic
// machinery and the cited dependency subclauses (§37.3.7 lifetime and memory
// allocation, §37.25 typespecs, §38.19/§38.20 access by index, §38.34 value).
// The three relations that carry §37.27's own normative details are exercised
// here through the public iterate/scan API:
//   detail 1 - vpiWaitingProcesses reaches the threads of the waiting
//   processes; detail 2 - vpiIndex on a named event reaches its array indices,
//   innermost
//              first, and is NULL when the named event is not an array element;
//   detail 3 - vpiRange on a named event array walks the unpacked range
//              declarations from leftmost to rightmost.

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

// Detail 1: vpiWaitingProcesses on a named event returns all the waiting
// processes identified by their threads, skipping unrelated children, even
// though the relation is named for the processes and not for the thread type.
TEST(NamedEventModel, WaitingProcessesIterationReachesWaitingThreads) {
  VpiContext ctx;

  VpiObject static_proc;
  static_proc.type = vpiThread;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject dynamic_proc;
  dynamic_proc.type = vpiThread;

  VpiObject event;
  event.type = vpiNamedEvent;
  event.children = {&static_proc, &typespec, &dynamic_proc};

  std::vector<VpiHandle> waiting =
      Collect(ctx, ctx.Iterate(vpiWaitingProcesses, &event));
  ASSERT_EQ(waiting.size(), 2u);
  EXPECT_EQ(waiting[0], &static_proc);
  EXPECT_EQ(waiting[1], &dynamic_proc);
}

// Detail 2: vpiIndex on a named event that is an array element returns its
// index expressions, beginning with the index for the named event and working
// outward.
TEST(NamedEventModel, IndexIterationReachesArrayIndicesOutward) {
  VpiContext ctx;

  VpiObject inner_index;
  inner_index.type = vpiConstant;
  VpiObject outer_index;
  outer_index.type = vpiConstant;

  VpiObject element;
  element.type = vpiNamedEvent;
  element.children = {&inner_index, &outer_index};

  std::vector<VpiHandle> indices =
      Collect(ctx, ctx.Iterate(vpiIndex, &element));
  ASSERT_EQ(indices.size(), 2u);
  EXPECT_EQ(indices[0], &inner_index);
  EXPECT_EQ(indices[1], &outer_index);
}

// Detail 2: a named event that is not part of an array has no indices, so
// iterating vpiIndex returns NULL.
TEST(NamedEventModel, IndexIterationIsNullWhenNotAnArrayElement) {
  VpiContext ctx;

  VpiObject standalone;
  standalone.type = vpiNamedEvent;
  EXPECT_EQ(ctx.Iterate(vpiIndex, &standalone), nullptr);
}

// Detail 3: vpiRange on a named event array walks the unpacked range
// declarations from the leftmost range through to the rightmost.
TEST(NamedEventModel, RangeIterationWalksUnpackedRangesLeftToRight) {
  VpiContext ctx;

  VpiObject leftmost;
  leftmost.type = vpiRange;
  VpiObject rightmost;
  rightmost.type = vpiRange;

  VpiObject array;
  array.type = vpiNamedEventArray;
  array.children = {&leftmost, &rightmost};

  std::vector<VpiHandle> ranges = Collect(ctx, ctx.Iterate(vpiRange, &array));
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_EQ(ranges[0], &leftmost);
  EXPECT_EQ(ranges[1], &rightmost);
}

// Details 1 and 2 select distinct targets: when a named event carries both a
// waiting thread and an array index, vpiWaitingProcesses reaches only the
// thread and vpiIndex reaches only the index expression - the two special
// relations do not cross-contaminate.
TEST(NamedEventModel, WaitingAndIndexRelationsSelectDistinctTargets) {
  VpiContext ctx;

  VpiObject waiter;
  waiter.type = vpiThread;
  VpiObject index;
  index.type = vpiConstant;

  VpiObject event;
  event.type = vpiNamedEvent;
  event.children = {&waiter, &index};

  std::vector<VpiHandle> waiting =
      Collect(ctx, ctx.Iterate(vpiWaitingProcesses, &event));
  ASSERT_EQ(waiting.size(), 1u);
  EXPECT_EQ(waiting[0], &waiter);

  std::vector<VpiHandle> indices = Collect(ctx, ctx.Iterate(vpiIndex, &event));
  ASSERT_EQ(indices.size(), 1u);
  EXPECT_EQ(indices[0], &index);
}

// -----------------------------------------------------------------------------
// The two typespec edges. §37.27 draws a named event to its event typespec and
// a named event array to its array typespec, both to the `typespec` class
// §37.25 fills with the concrete typespec kinds. §37.4.1 makes that enclosure a
// grouping rather than an object, so vpiTypespec is the group's name; matching
// it against an object's own type, which is what the generic traversal does,
// reached the typespec of no named event any design declares.
// -----------------------------------------------------------------------------

// Class membership: the kinds the enclosure holds are the concrete typespecs
// §37.25 draws inside it, which is what the edge has to reach. An object of
// some other kind is not one of them.
TEST(NamedEventModel, TheTypespecClassGroupsTheConcreteTypespecKinds) {
  EXPECT_TRUE(VpiIsTypespecType(vpiEventTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiStructTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiTypeParameter));

  EXPECT_FALSE(VpiIsTypespecType(vpiNamedEvent));
  EXPECT_FALSE(VpiIsTypespecType(vpiThread));
}

// §37.27 (figure, named event --vpiTypespec--> event typespec): a named event
// reaches the event typespec drawn on it. A waiting thread hanging off the same
// event, which the diagram reaches by an edge of its own, is not it.
TEST(NamedEventModel, ANamedEventReachesItsEventTypespec) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject waiter;
  waiter.type = vpiThread;
  VpiObject typespec;
  typespec.type = vpiEventTypespec;

  VpiObject event;
  event.type = vpiNamedEvent;
  event.children = {&waiter, &typespec};

  EXPECT_EQ(vpi_handle(vpiTypespec, &event), &typespec);

  SetGlobalVpiContext(nullptr);
}

// §37.27 (figure, named event array --vpiTypespec--> array typespec): the array
// reaches the array typespec drawn on it, by the same edge and the same class.
// A range declaration, which detail 3 reaches by its own iteration, is not it.
TEST(NamedEventModel, ANamedEventArrayReachesItsArrayTypespec) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject range;
  range.type = vpiRange;
  VpiObject typespec;
  typespec.type = vpiArrayTypespec;

  VpiObject array;
  array.type = vpiNamedEventArray;
  array.children = {&range, &typespec};

  EXPECT_EQ(vpi_handle(vpiTypespec, &array), &typespec);

  SetGlobalVpiContext(nullptr);
}

// §37.27 (figure): a named event declared with no typespec reaches none, rather
// than some other object hanging off it.
TEST(NamedEventModel, ANamedEventWithNoTypespecReachesNone) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject waiter;
  waiter.type = vpiThread;

  VpiObject event;
  event.type = vpiNamedEvent;
  event.children = {&waiter};

  EXPECT_EQ(vpi_handle(vpiTypespec, &event), nullptr);

  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
