#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, OverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);

  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
}

TEST(SvaEngine, NonOverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
}

TEST(SvaEngine, PropertyPendingResolvesPass) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(true);
  EXPECT_EQ(resolved, PropertyResult::kPass);
}

TEST(SvaEngine, PropertyPendingResolvesFail) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(false);
  EXPECT_EQ(resolved, PropertyResult::kFail);
}

TEST(SvaEngine, NonOverlappingEmptyAntecedentMatchResolvesImmediately) {
  EXPECT_EQ(EvalImplication(true, true, true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, true, true), PropertyResult::kFail);
  EXPECT_EQ(EvalImplication(true, true, true, false), PropertyResult::kPending);
}

TEST(SvaEngine, ImplicationHoldsOnlyIfEveryAntecedentMatchConsequentHolds) {
  EXPECT_EQ(EvalImplicationOverMatches({}), PropertyResult::kVacuousPass);

  EXPECT_EQ(EvalImplicationOverMatches({PropertyResult::kPass}),
            PropertyResult::kPass);

  EXPECT_EQ(EvalImplicationOverMatches({PropertyResult::kPass,
                                        PropertyResult::kVacuousPass,
                                        PropertyResult::kPass}),
            PropertyResult::kPass);

  EXPECT_EQ(
      EvalImplicationOverMatches({PropertyResult::kPass, PropertyResult::kFail,
                                  PropertyResult::kPass}),
      PropertyResult::kFail);
}

TEST(SvaEngine, NoAntecedentMatchHoldsVacuouslyRegardlessOfConsequent) {
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

std::string ImplicationSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic req, gnt, ack, done, late;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign req = tick inside {1, 2, 4};\n"
         "  assign gnt = tick inside {1, 4};\n"
         "  assign ack = tick inside {2, 3};\n"
         "  assign done = tick inside {2, 3};\n"
         "  assign late = tick inside {2};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(ImplicationProperty, OverlappedConsequentBeginsAtTheMatchEndPoint) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |-> gnt) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(ImplicationProperty, NonoverlappedConsequentBeginsAtTheNextTick) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |=> gnt) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
}

TEST(ImplicationProperty, EveryMatchOfTheAntecedentMustHold) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) (req ##[1:2] "
                        "ack) |-> done) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 4u);
  SimFixture g;
  auto* one_fails = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) (req ##[1:2] "
                        "ack) |-> late) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(one_fails, nullptr);
  EXPECT_EQ(one_fails->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(ImplicationProperty, ConsequentIsAnyProperty) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |-> gnt or "
                        "ack) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

}  // namespace
