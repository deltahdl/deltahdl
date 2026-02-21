// Tests for A.7.4 — Specify path delays — Simulation

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

struct SimA704Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src,
                                 SimA704Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.7.4 Simulation — path delays do not interfere
// =============================================================================

// Module with 6-delay path simulates correctly
TEST(SimA704, SixDelayPathSimulates) {
  SimA704Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// Module with 12-delay path simulates correctly
TEST(SimA704, TwelveDelayPathSimulates) {
  SimA704Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// Module with min:typ:max delay simulates correctly
TEST(SimA704, MinTypMaxDelaySimulates) {
  SimA704Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// =============================================================================
// A.7.4 Runtime PathDelay with delay_count
// =============================================================================

// PathDelay with delay_count=6 stores 6 transition delays
TEST(SimA704, RuntimePathDelaySixDelays) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delay_count = 6;
  pd.delays[0] = 1;   // t01
  pd.delays[1] = 2;   // t10
  pd.delays[2] = 3;   // t0z
  pd.delays[3] = 4;   // tz1
  pd.delays[4] = 5;   // t1z
  pd.delays[5] = 6;   // tz0
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("a", "b"));
  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 1u);
  EXPECT_EQ(mgr.PathDelayCount(), 1u);

  auto& delays = mgr.GetPathDelays();
  ASSERT_EQ(delays.size(), 1u);
  EXPECT_EQ(delays[0].delay_count, 6u);
  EXPECT_EQ(delays[0].delays[0], 1u);
  EXPECT_EQ(delays[0].delays[3], 4u);
  EXPECT_EQ(delays[0].delays[5], 6u);
}

// PathDelay with delay_count=12 stores 12 transition delays
TEST(SimA704, RuntimePathDelayTwelveDelays) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "in";
  pd.dst_port = "out";
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) {
    pd.delays[i] = static_cast<uint64_t>(i + 1);
  }
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("in", "out"));
  auto& delays = mgr.GetPathDelays();
  ASSERT_EQ(delays.size(), 1u);
  EXPECT_EQ(delays[0].delay_count, 12u);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(delays[0].delays[i], static_cast<uint64_t>(i + 1));
  }
}

// Backward compatibility: delay_count=1 with single delay in delays[0]
TEST(SimA704, RuntimePathDelaySingleDelay) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delay_count = 1;
  pd.delays[0] = 10;
  mgr.AddPathDelay(pd);

  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 10u);
}
