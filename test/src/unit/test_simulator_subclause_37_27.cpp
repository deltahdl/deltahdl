#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

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

TEST(NamedEventModel, IndexIterationIsNullWhenNotAnArrayElement) {
  VpiContext ctx;

  VpiObject standalone;
  standalone.type = vpiNamedEvent;
  EXPECT_EQ(ctx.Iterate(vpiIndex, &standalone), nullptr);
}

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

TEST(NamedEventModel, TheTypespecClassGroupsTheConcreteTypespecKinds) {
  EXPECT_TRUE(VpiIsTypespecType(vpiEventTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiStructTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiTypeParameter));
  for (int kind : {vpiChandleTypespec, vpiIntegerTypespec, vpiTimeTypespec,
                   vpiRealTypespec}) {
    EXPECT_TRUE(VpiIsTypespecType(kind));
  }

  EXPECT_FALSE(VpiIsTypespecType(vpiNamedEvent));
  EXPECT_FALSE(VpiIsTypespecType(vpiThread));
}

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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&event))),
            &typespec);

  SetGlobalVpiContext(nullptr);
}

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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&array))),
            &typespec);

  SetGlobalVpiContext(nullptr);
}

TEST(NamedEventModel, ANamedEventWithNoTypespecReachesNone) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject waiter;
  waiter.type = vpiThread;

  VpiObject event;
  event.type = vpiNamedEvent;
  event.children = {&waiter};

  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&event)), nullptr);

  SetGlobalVpiContext(nullptr);
}

class NamedEventsOfARun : public VpiDesignRun {
 protected:
  static int KindOf(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }
};

constexpr const char* kEvents =
    "module top;\n"
    "  event e, f, g;\n"
    "  event ea [2];\n"
    "  initial @e;\n"
    "  initial @(e or f);\n"
    "  initial @(g or e);\n"
    "  initial begin @f; end\n"
    "  initial begin #1 -> f; end\n"
    "endmodule\n";

TEST_F(NamedEventsOfARun, AnEventAndAnEventArrayReachTheirTypespecs) {
  Run(kEvents);
  EXPECT_EQ(KindOf(vpiTypespec, By("top.e")), vpiEventTypespec);
  vpiHandle array = vpi_handle(vpiTypespec, By("top.ea"));
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, array), vpiArrayTypespec);
  EXPECT_EQ(KindOf(vpiElemTypespec, array), vpiEventTypespec);
}

TEST_F(NamedEventsOfARun, AnEventArraysElementsAreNamedEvents) {
  Run(kEvents);
  vpiHandle array = By("top.ea");
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, array), vpiNamedEventArray);
  vpiHandle element = vpi_handle_by_index(array, 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiNamedEvent);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, element)), VpiObjectOf(array));
}

TEST_F(NamedEventsOfARun, AnEventReachesTheThreadsWaitingOnIt) {
  Run(kEvents);
  EXPECT_EQ(ObjectsOf(vpiWaitingProcesses, By("top.e")).size(), 2U);
  EXPECT_TRUE(ObjectsOf(vpiWaitingProcesses, By("top.f")).empty());
}

}  // namespace
}  // namespace delta
