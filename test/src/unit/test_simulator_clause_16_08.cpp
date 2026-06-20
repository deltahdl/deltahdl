#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NamedSequenceLowering, EndPointVariableIsCreated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("ab"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_ab");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

TEST(NamedSequenceLowering, MultipleSequencesEachGetEndPoint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence first;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence second;\n"
      "    @(posedge clk) b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("__seq_first"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("__seq_second"), nullptr);
}

}  // namespace
