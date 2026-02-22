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

struct SimA608Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA608Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// Simulation tests — A.6.8 Looping statements
// =============================================================================

// --- forever ---

// §12.7.7: forever loop — exits via break
TEST(SimA608, ForeverBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    forever begin\n"
                              "      if (x == 8'd5) break;\n"
                              "      x = x + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.7: forever with continue skips to next iteration
TEST(SimA608, ForeverContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x, count;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    count = 8'd0;\n"
                              "    forever begin\n"
                              "      x = x + 8'd1;\n"
                              "      if (x == 8'd10) break;\n"
                              "      if (x[0]) continue;\n"
                              "      count = count + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // x goes 1,2,3,...,10. Even values (2,4,6,8) reach count increment = 4
  EXPECT_EQ(count->value.ToUint64(), 4u);
}

// --- repeat ---

// §12.7.6: repeat(N) executes body exactly N times
TEST(SimA608, RepeatCount) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    repeat (5) x = x + 8'd1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.6: repeat(0) executes body zero times
TEST(SimA608, RepeatZero) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd42;\n"
                              "    repeat (0) x = 8'd99;\n"
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

// §12.7.6: repeat with break exits early
TEST(SimA608, RepeatBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    repeat (100) begin\n"
                              "      if (x == 8'd3) break;\n"
                              "      x = x + 8'd1;\n"
                              "    end\n"
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

// §12.7.6: repeat with continue skips remainder
TEST(SimA608, RepeatContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x, count;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    count = 8'd0;\n"
                              "    repeat (5) begin\n"
                              "      x = x + 8'd1;\n"
                              "      if (x == 8'd3) continue;\n"
                              "      count = count + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // 5 iterations, skip iteration 3 => count = 4
  EXPECT_EQ(count->value.ToUint64(), 4u);
}

// --- while ---

// §12.7.4: while loop — accumulate sum
TEST(SimA608, WhileBasic) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd10;\n"
                              "    while (x > 0) x = x - 8'd1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §12.7.4: while loop — condition false initially, zero iterations
TEST(SimA608, WhileZeroIter) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd42;\n"
                              "    while (0) x = 8'd99;\n"
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

// §12.7.4: while with break exits early
TEST(SimA608, WhileBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    while (1) begin\n"
                              "      if (x == 8'd7) break;\n"
                              "      x = x + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §12.7.4: while with continue
TEST(SimA608, WhileContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x, count;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    count = 8'd0;\n"
                              "    while (x < 8'd6) begin\n"
                              "      x = x + 8'd1;\n"
                              "      if (x == 8'd3) continue;\n"
                              "      count = count + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // 6 iterations (x = 1..6), skip x==3 => count = 5
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

// --- for ---

// §12.7.1: for loop — basic accumulation
TEST(SimA608, ForBasic) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] total;\n"
                              "  initial begin\n"
                              "    total = 8'd0;\n"
                              "    for (int i = 0; i < 5; i = i + 1)\n"
                              "      total = total + 8'd1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.1: for with typed init — variable used in body
TEST(SimA608, ForTypedInit) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] sum;\n"
                              "  initial begin\n"
                              "    sum = 8'd0;\n"
                              "    for (int i = 1; i <= 4; i = i + 1)\n"
                              "      sum = sum + i[7:0];\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  // 1 + 2 + 3 + 4 = 10
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.7.1: for with break exits early
TEST(SimA608, ForBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    for (int i = 0; i < 100; i = i + 1) begin\n"
                              "      if (i == 3) break;\n"
                              "      x = x + 8'd1;\n"
                              "    end\n"
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

// §12.7.1: for with continue skips to step
TEST(SimA608, ForContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] count;\n"
                              "  initial begin\n"
                              "    count = 8'd0;\n"
                              "    for (int i = 0; i < 6; i = i + 1) begin\n"
                              "      if (i == 2 || i == 4) continue;\n"
                              "      count = count + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  // 6 iterations, skip i==2 and i==4 => count = 4
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §12.7.1: for with empty init/cond/step — for(;;) with break
TEST(SimA608, ForAllEmptyWithBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    for (;;) begin\n"
                              "      if (x == 8'd4) break;\n"
                              "      x = x + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §12.7.1: for_step with inc_or_dec_expression (i++)
TEST(SimA608, ForStepIncrement) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    for (int i = 0; i < 3; i++)\n"
                              "      x = x + 8'd1;\n"
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

// --- do-while ---

// §12.7.5: do-while executes body at least once
TEST(SimA608, DoWhileAtLeastOnce) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    do x = x + 8'd1; while (0);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Body executes once even though condition is false
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.7.5: do-while iterates until condition becomes false
TEST(SimA608, DoWhileIterates) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    do x = x + 8'd1; while (x < 8'd5);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.5: do-while with break
TEST(SimA608, DoWhileBreak) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    do begin\n"
                              "      x = x + 8'd1;\n"
                              "      if (x == 8'd3) break;\n"
                              "    end while (1);\n"
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

// §12.7.5: do-while with continue
TEST(SimA608, DoWhileContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x, count;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    count = 8'd0;\n"
                              "    do begin\n"
                              "      x = x + 8'd1;\n"
                              "      if (x == 8'd3) continue;\n"
                              "      count = count + 8'd1;\n"
                              "    end while (x < 8'd5);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // 5 iterations (x=1..5), skip x==3 => count = 4
  EXPECT_EQ(count->value.ToUint64(), 4u);
}

// --- foreach ---

// §12.7.3: foreach iterates over array elements
TEST(SimA608, ForeachBasic) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] arr [4];\n"
                              "  logic [7:0] total;\n"
                              "  initial begin\n"
                              "    arr[0] = 8'd1;\n"
                              "    arr[1] = 8'd2;\n"
                              "    arr[2] = 8'd3;\n"
                              "    arr[3] = 8'd4;\n"
                              "    total = 8'd0;\n"
                              "    foreach (arr[i]) total = total + arr[i];\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  // 1 + 2 + 3 + 4 = 10
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// --- Nested loops ---

// Nested loops: inner break doesn't affect outer
TEST(SimA608, NestedLoopInnerBreak) {
  SimA608Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] outer_count;\n"
                   "  initial begin\n"
                   "    outer_count = 8'd0;\n"
                   "    for (int i = 0; i < 3; i = i + 1) begin\n"
                   "      for (int j = 0; j < 100; j = j + 1) begin\n"
                   "        if (j == 2) break;\n"
                   "      end\n"
                   "      outer_count = outer_count + 8'd1;\n"
                   "    end\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("outer_count");
  ASSERT_NE(var, nullptr);
  // Outer loop runs 3 times despite inner break
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// Nested loops: inner continue doesn't affect outer
TEST(SimA608, NestedLoopInnerContinue) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] total;\n"
                              "  initial begin\n"
                              "    total = 8'd0;\n"
                              "    for (int i = 0; i < 3; i = i + 1) begin\n"
                              "      for (int j = 0; j < 4; j = j + 1) begin\n"
                              "        if (j == 1) continue;\n"
                              "        total = total + 8'd1;\n"
                              "      end\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  // 3 outer * (4 inner - 1 skipped) = 3 * 3 = 9
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// Mixed loop types: repeat inside for
TEST(SimA608, MixedRepeatInsideFor) {
  SimA608Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  initial begin\n"
                              "    x = 8'd0;\n"
                              "    for (int i = 0; i < 3; i = i + 1) begin\n"
                              "      repeat (2) x = x + 8'd1;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // 3 outer * 2 inner = 6
  EXPECT_EQ(var->value.ToUint64(), 6u);
}
