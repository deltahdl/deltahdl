#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ProceduralBlockSim, InitialConstructRuns) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial a = 8'd17;\n"
                      "endmodule\n",
                      "a"),
            17u);
}

TEST(ProceduralBlockSim, FinalConstructLowersWithoutDisturbingInitial) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial a = 8'd1;\n"
                      "  final a = 8'd99;\n"
                      "endmodule\n",
                      "a"),
            1u);
}

TEST(ProceduralBlockSim, BlockingAssignmentSimple) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial x = 5;\n"
                      "endmodule\n",
                      "x"),
            5u);
}

TEST(ProceduralBlockSim, NonblockingAssignmentInInitial) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] q;\n"
                      "  initial begin\n"
                      "    q <= 8'd55;\n"
                      "  end\n"
                      "endmodule\n",
                      "q"),
            55u);
}

TEST(ProceduralBlockSim, AlwaysCombComputesOutput) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [3:0] a, b;\n"
                      "  logic [3:0] y;\n"
                      "  initial begin a = 4'b1100; b = 4'b1010; end\n"
                      "  always_comb y = a & b;\n"
                      "endmodule\n",
                      "y"),
            0b1000u);
}

TEST(ProceduralBlockSim, ProceduralForceOverridesValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial begin\n"
                      "    a = 8'd1;\n"
                      "    force a = 8'd77;\n"
                      "  end\n"
                      "endmodule\n",
                      "a"),
            77u);
}

TEST(ProceduralBlockSim, ProceduralReleaseRestoresValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial begin\n"
                      "    a = 8'd1;\n"
                      "    force a = 8'd77;\n"
                      "    release a;\n"
                      "    a = 8'd9;\n"
                      "  end\n"
                      "endmodule\n",
                      "a"),
            9u);
}

TEST(ProceduralBlockSim, ProceduralAssignThenDeassign) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a, b;\n"
                      "  initial begin\n"
                      "    b = 8'd11;\n"
                      "    assign a = b;\n"
                      "    deassign a;\n"
                      "    a = 8'd33;\n"
                      "  end\n"
                      "endmodule\n",
                      "a"),
            33u);
}

TEST(ProceduralBlockSim, IncDecExpressionCrossLinkPostfix) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer i;\n"
                      "  initial begin\n"
                      "    i = 7;\n"
                      "    i++;\n"
                      "    i++;\n"
                      "  end\n"
                      "endmodule\n",
                      "i"),
            9u);
}

TEST(ProceduralBlockSim, IncDecExpressionCrossLinkPrefix) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer i;\n"
                      "  initial begin\n"
                      "    i = 5;\n"
                      "    --i;\n"
                      "  end\n"
                      "endmodule\n",
                      "i"),
            4u);
}

TEST(ProceduralBlockSim, NonblockingAssignmentWithDelaySchedules) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] q;\n"
                      "  initial begin\n"
                      "    q = 8'd0;\n"
                      "    q <= #5 8'd55;\n"
                      "  end\n"
                      "endmodule\n",
                      "q"),
            55u);
}

TEST(ProceduralBlockSim, ProceduralForceOnNetOverridesValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire [7:0] w;\n"
                      "  initial force w = 8'd42;\n"
                      "endmodule\n",
                      "w"),
            42u);
}

TEST(ProceduralBlockSim, ProceduralReleaseOnNetRestoresDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire [7:0] w;\n"
                      "  assign w = 8'd7;\n"
                      "  initial begin\n"
                      "    force w = 8'd42;\n"
                      "    release w;\n"
                      "  end\n"
                      "endmodule\n",
                      "w"),
            7u);
}

TEST(ProceduralBlockSim, AllAssignmentOperatorsInSequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer a, b, c, d, e, g, h, i, j, k, l, mm;\n"
      "  initial begin\n"
      "    a = 10; a += 5;\n"
      "    b = 10; b -= 5;\n"
      "    c = 10; c *= 2;\n"
      "    d = 10; d /= 2;\n"
      "    e = 10; e %= 3;\n"
      "    g = 8'hFF; g &= 8'h0F;\n"
      "    h = 8'h00; h |= 8'h01;\n"
      "    i = 8'h0F; i ^= 8'hF0;\n"
      "    j = 1;    j <<= 3;\n"
      "    k = 16;   k >>= 2;\n"
      "    l = 1;    l <<<= 2;\n"
      "    mm = 16;  mm >>>= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {
                       {"a", 15u},
                       {"b", 5u},
                       {"c", 20u},
                       {"d", 5u},
                       {"e", 1u},
                       {"g", 0x0Fu},
                       {"h", 0x01u},
                       {"i", 0xFFu},
                       {"j", 8u},
                       {"k", 4u},
                       {"l", 4u},
                       {"mm", 8u},
                   });
}

}  // namespace
