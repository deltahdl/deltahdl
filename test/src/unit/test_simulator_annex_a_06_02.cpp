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
  // §9.2.3: final procedures are enabled at the end of simulation and execute
  // only once. The initial block sets a = 1, then the final block runs at end
  // of simulation and overwrites it with 99, so the observed end value is 99.
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial a = 8'd1;\n"
                      "  final a = 8'd99;\n"
                      "endmodule\n",
                      "a"),
            99u);
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

// blocking_assignment whose variable_lvalue is a concatenation (§A.8.5 real
// syntax): a single right-hand side is split across the concatenated targets.
// Built from source and run through the full pipeline so the observed values
// come from the assignment executing, not a hand-built state.
TEST(ProceduralBlockSim, BlockingAssignmentConcatLvalue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  initial {hi, lo} = 8'hC3;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"hi", 0xCu}, {"lo", 0x3u}});
}

// blocking_assignment alt 1: variable_lvalue = delay_or_event_control
// expression. The intra-assignment delay is mandatory in this alternative;
// running to quiescence observes the delayed assignment taking effect.
TEST(ProceduralBlockSim, BlockingAssignmentIntraDelayRuns) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a;\n"
                      "  initial begin\n"
                      "    a = 8'd0;\n"
                      "    a = #5 8'd42;\n"
                      "  end\n"
                      "endmodule\n",
                      "a"),
            42u);
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
