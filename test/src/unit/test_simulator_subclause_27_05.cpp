#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GenerateSimulation, GenerateIfTrueBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 1) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 0;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(GenerateSimulation, GenerateIfFalseBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 0) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(GenerateSimulation, GenerateCaseMatch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      3: begin assign x = 30; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(GenerateSimulation, GenerateCaseDefault) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 99) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      default: begin assign x = 77; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(GenerateSimulation, GenerateIfNoElseFalse) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter EN = 0) ();\n"
      "  logic [31:0] x;\n"
      "  assign x = 5;\n"
      "  generate\n"
      "    if (EN) begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(GenerateSimulation, GenerateCaseNoMatchNoDefault) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter MODE = 42) ();\n"
      "  logic [31:0] x;\n"
      "  assign x = 3;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(GenerateSimulation, GenerateIfElseIfChainSelectsMiddle) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 1) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (SEL == 0) begin\n"
      "      assign x = 10;\n"
      "    end else if (SEL == 1) begin\n"
      "      assign x = 55;\n"
      "    end else begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(GenerateSimulation, GenerateCaseMultiplePatternsPerItem) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (SEL)\n"
      "      0, 1, 2: begin assign x = 11; end\n"
      "      default: begin assign x = 88; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(GenerateSimulation, GenvarGatedConditionalDrivesValue) {
  // §27.5 end-to-end over the §27.4 loop-generate dependency: a conditional
  // generate nested in a loop generate is selected per iteration using the
  // loop genvar as its constant. Only the i==2 iteration takes the (else-less)
  // then-branch, so exactly one continuous assignment to the module-level
  // result survives; the others select nothing. The input is built from real
  // loop-generate syntax and driven through the full pipeline, and the selected
  // block's assignment is observed by its simulated result.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t ();\n"
      "  logic [31:0] r;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "      if (i == 2) begin\n"
      "        assign r = 77;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(GenerateSimulation, GenerateIfElseIfChainSelectsFinalElse) {
  // §27.5 requires a conditional generate construct to select "at most one
  // generate block from a set of alternative generate blocks based on constant
  // expressions evaluated during elaboration", and to instantiate the selected
  // block into the model. Here no condition in the chain holds, so the final
  // else is the selected alternative and its 64 is the only value driven onto
  // the module-level variable the simulated run reads back. Elaborating the
  // else arm's body without evaluating the nested condition instantiates the
  // first else-if branch instead and yields 41, and never reaches the two
  // alternatives past it, so each of the four constants is distinct and
  // non-zero to name which alternative a wrong run selected.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter SEL = 7) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (SEL == 0) begin\n"
      "      assign x = 13;\n"
      "    end else if (SEL == 1) begin\n"
      "      assign x = 41;\n"
      "    end else if (SEL == 2) begin\n"
      "      assign x = 26;\n"
      "    end else begin\n"
      "      assign x = 64;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 64u);
}

}  // namespace
