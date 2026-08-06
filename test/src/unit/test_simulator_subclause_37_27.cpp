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

}  // namespace
}  // namespace delta
