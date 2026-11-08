#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombLowering, AlwaysCombRetrigger) {
  LowerFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 6u);
}

TEST(AlwaysCombLowering, AlwaysCombAutoTriggerTimeZero) {
  LowerFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] b;\n"
      "  always_comb b = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(AlwaysCombSim, ConcurrentAlwaysCombBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd10;\n"
      "  always_comb r1 = a + 8'd1;\n"
      "  always_comb r2 = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 12u);
}

TEST(AlwaysCombSim, AlwaysCombWithBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    r1 = a + 8'd1;\n"
      "    r2 = a + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 7u);
}

TEST(AlwaysCombSim, AlwaysCombTriggersAfterInitial) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd99;\n"
      "  always_comb b = a;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 99u);
}

TEST(AlwaysCombSim, TheTimeZeroEvaluationFollowsTheInitialProcedures) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic a, y;\n"
                       "  always_comb begin y = a; $display(\"y=%b\", y); end\n"
                       "  initial a = 1;\n"
                       "endmodule\n",
                       f),
            "y=1\n");
}

TEST(AlwaysCombSim, AlwaysCombRetriggersOnChange) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a = 8'd10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 11u);
}

void ExpectAlwaysCombRunCount(const char* src, uint64_t expected_runs) {
  SimFixture f;
  auto* runs = RunAndFindVar(src, f, "runs");
  ASSERT_NE(runs, nullptr);
  EXPECT_EQ(runs->value.ToUint64(), expected_runs);
}

TEST(AlwaysCombSim,
     AlwaysCombDoesNotRetriggerWhenAnOutOfBoundsBitSelectWriteChangesNothing) {
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a[9] = 1'b1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      1);
}

TEST(AlwaysCombSim,
     AlwaysCombRetriggersWhenAnInBoundsBitSelectWriteChangesTheVector) {
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a[3] = 1'b1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      2);
}

TEST(AlwaysCombSim,
     AlwaysCombDoesNotRetriggerWhenAWriteDepositsTheValueTheVariableHolds) {
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #1 a = 8'd5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      1);
}

TEST(AlwaysCombSim, AlwaysCombRetriggersWhenAWriteChangesTheVariable) {
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #1 a = 8'd7;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      2);
}

TEST(AlwaysCombSim, AlwaysCombMuxPattern) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 22u);
}

TEST(AlwaysCombBasicSim, AlwaysCombResultWidth8) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    result = a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(AlwaysCombSim, AlwaysCombNonblockingIntraDelay) {
  SimFixture f;
  auto* d = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, d;\n"
      "  always_comb d <= #1 b & c;\n"
      "  initial begin\n"
      "    b = 8'hF0;\n"
      "    c = 8'h3C;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 0x30u);
}

TEST(AlwaysCombSim, AlwaysCombChainedDependency) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  always_comb b = a + 8'd1;\n"
      "  always_comb c = b + 8'd1;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a = 8'd10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 12u);
}

TEST(AlwaysCombSim, AlwaysCombRetriggersOnAnIncrementOperatorWrite) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  logic [7:0] y;\n"
      "  always_comb y = i + 8'd1;\n"
      "  initial begin\n"
      "    i = 7;\n"
      "    #1 i++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
}

}  // namespace
