// Tests for A.7.5.2 — System timing check command arguments — Simulation

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
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA70502Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA70502Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// A.7.5.2 Sim — $nochange with mintypmax offsets simulates
// =============================================================================

TEST(SimA70502, NochangeMinTypMaxOffsetsSimulates) {
  SimA70502Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] x;\n"
                   "  specify\n"
                   "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
                   "  endspecify\n"
                   "  initial x = 8'd10;\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// =============================================================================
// A.7.5.2 Sim — $setuphold with mintypmax timestamp_condition simulates
// =============================================================================

TEST(SimA70502, SetupholdMinTypMaxConditionsSimulates) {
  SimA70502Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
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

// =============================================================================
// A.7.5.2 Sim — delayed_data with bracket index simulates
// =============================================================================

TEST(SimA70502, DelayedDataBracketSimulates) {
  SimA70502Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dD[3]);\n"
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
// A.7.5.2 Sim — $timeskew with remain_active_flag mintypmax simulates
// =============================================================================

TEST(SimA70502, RemainActiveFlagMinTypMaxSimulates) {
  SimA70502Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 1:2:3);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}
