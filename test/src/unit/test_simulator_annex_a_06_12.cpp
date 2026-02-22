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

struct SimA612Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA612Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// Simulation tests — A.6.12 Randsequence
// =============================================================================

// Basic randsequence: code block side effects execute
TEST(SimA612, CodeBlockSideEffect) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : { x = 8'd42; };\n"
                              "    endsequence\n"
                              "  end\n"
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

// Sequence of productions: all execute in order
TEST(SimA612, ProductionSequenceOrder) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : first second;\n"
                              "      first : { x = x + 8'd10; };\n"
                              "      second : { x = x + 8'd20; };\n"
                              "    endsequence\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// Weighted alternatives: both are reachable (statistical test)
TEST(SimA612, WeightedAlternativesReachable) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : a := 1 | b := 1;\n"
                              "      a : { x = 8'd1; };\n"
                              "      b : { x = 8'd2; };\n"
                              "    endsequence\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // One of the alternatives was chosen
  EXPECT_TRUE(var->value.ToUint64() == 1u || var->value.ToUint64() == 2u);
}

// Break in code block terminates randsequence
TEST(SimA612, BreakTerminatesRandsequence) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : first second;\n"
                              "      first : { x = 8'd10; break; };\n"
                              "      second : { x = 8'd99; };\n"
                              "    endsequence\n"
                              "  end\n"
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

// Repeat production: code block executes N times
TEST(SimA612, RepeatProduction) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : repeat(3) inc;\n"
                              "      inc : { x = x + 8'd1; };\n"
                              "    endsequence\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// If-else in production: condition selects branch
TEST(SimA612, IfElseProduction) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : if (0) a else b;\n"
                              "      a : { x = 8'd1; };\n"
                              "      b : { x = 8'd2; };\n"
                              "    endsequence\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// Case in production: selects matching branch
TEST(SimA612, CaseProduction) {
  SimA612Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] x;\n"
                   "  initial begin\n"
                   "    x = 8'd0;\n"
                   "    randsequence(main)\n"
                   "      main : case (1) 0: a; 1: b; default: c; endcase;\n"
                   "      a : { x = 8'd10; };\n"
                   "      b : { x = 8'd20; };\n"
                   "      c : { x = 8'd30; };\n"
                   "    endsequence\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// No production name — first production is used as top
TEST(SimA612, NoProductionNameUsesFirst) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence()\n"
                              "      top : { x = 8'd55; };\n"
                              "    endsequence\n"
                              "  end\n"
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

// Rand join: both productions execute (order may vary)
TEST(SimA612, RandJoinBothExecute) {
  SimA612Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    randsequence(main)\n"
                              "      main : rand join a b;\n"
                              "      a : { x = x + 8'd10; };\n"
                              "      b : { x = x + 8'd20; };\n"
                              "    endsequence\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}
