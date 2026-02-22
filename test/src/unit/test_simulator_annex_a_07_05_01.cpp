// Tests for A.7.5.1 — System timing check commands — Simulation

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA70501Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimA70501Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.7.5.1 Runtime — $setuphold dual limits stored in TimingCheckEntry
// =============================================================================

TEST(SimA70501, SetupholdDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  tc.limit2 = 5;
  tc.notifier = "ntfr";
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(stored.limit, 10u);
  EXPECT_EQ(stored.limit2, 5u);
  EXPECT_EQ(stored.notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 Runtime — $recrem dual limits stored
// =============================================================================

TEST(SimA70501, RecremDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = 8;
  tc.limit2 = 3;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(stored.limit, 8u);
  EXPECT_EQ(stored.limit2, 3u);
}

// =============================================================================
// A.7.5.1 Runtime — $fullskew dual limits stored
// =============================================================================

TEST(SimA70501, FullskewDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kFullskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 4;
  tc.limit2 = 6;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(stored.limit, 4u);
  EXPECT_EQ(stored.limit2, 6u);
}

// =============================================================================
// A.7.5.1 Runtime — $width threshold is second limit
// =============================================================================

TEST(SimA70501, WidthThresholdAsLimit2) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.limit2 = 1;  // threshold
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.limit2, 1u);
}

// =============================================================================
// A.7.5.1 Runtime — $nochange stores two offsets
// =============================================================================

TEST(SimA70501, NochangeOffsetsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.limit = 0;   // start_edge_offset
  tc.limit2 = 0;  // end_edge_offset
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kNochange);
}

// =============================================================================
// A.7.5.1 End-to-end — $setuphold with extended args simulates
// =============================================================================

TEST(SimA70501, SetupholdFullArgsSimulates) {
  SimA70501Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// =============================================================================
// A.7.5.1 End-to-end — $timeskew with flags simulates
// =============================================================================

TEST(SimA70501, TimeskewWithFlagsSimulates) {
  SimA70501Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}
