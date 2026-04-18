#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GenerateSimulation, GenerateIfTrueBranch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(GenerateSimulation, GenerateIfFalseBranch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(GenerateSimulation, GenerateCaseMatch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(GenerateSimulation, GenerateCaseDefault) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(GenerateSimulation, GenerateIfNoElseFalse) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter EN = 0) ();\n"
      "  logic [31:0] x;\n"
      "  assign x = 5;\n"
      "  generate\n"
      "    if (EN) begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(GenerateSimulation, GenerateCaseNoMatchNoDefault) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §27.5: else binds to the nearest preceding if, so in an if/else-if/else
// chain only the first branch whose condition holds contributes continuous
// assignments to the elaborated design.
TEST(GenerateSimulation, GenerateIfElseIfChainSelectsMiddle) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §27.5: a case-generate item selects its block when any of its listed
// constant expressions matches the controlling expression.
TEST(GenerateSimulation, GenerateCaseMultiplePatternsPerItem) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter SEL = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (SEL)\n"
      "      0, 1, 2: begin assign x = 11; end\n"
      "      default: begin assign x = 88; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

}  // namespace
