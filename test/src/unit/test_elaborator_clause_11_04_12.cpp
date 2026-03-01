// §11.4.12: Concatenation operators

#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// § concatenation with variables
TEST(SimA81, ConcatWithVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hC;\n"
      "    b = 4'h3;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC3u);
}

// § concatenation — does not interfere with other initial blocks
TEST(SimA81, ConcatDoesNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {4'h1, 4'h2};\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0x12u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}

// =============================================================================
// A.8.1 Concatenations — Elaboration
// =============================================================================
// § concatenation elaborates in continuous assignment
TEST(ElabA81, ConcatenationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  assign a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_concatenation in parameter initialization
TEST(ElabA81, ConstantConcatenationInParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [15:0] P = {8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
