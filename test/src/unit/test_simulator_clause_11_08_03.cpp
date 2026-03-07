#include "fixture_simulator.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §11.8.3: RHS sized to LHS width on assignment.
TEST(AssignEval, RhsSizedToLhsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin narrow = 4'hF; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  // 4'hF zero-extended to 8 bits = 8'h0F.
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// §11.8.3: Signed RHS sign-extends when assigned to wider LHS.
TEST(AssignEval, SignedRhsSignExtendsToLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin narrow = -4'sd1; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  // -1 in 4 signed bits sign-extended to 8 bits = 0xFF = -1.
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// §11.8.3: RHS truncated when wider than LHS.
TEST(AssignEval, WideRhsTruncated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  initial begin wide = 8'hAB; narrow = wide; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  // 8'hAB truncated to 4 bits = 4'hB.
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

}  // namespace
