#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TwoStateAndFourState, FourStateToTwoStateXBecomesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'bxxxx_xxxx;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, FourStateToTwoStateZBecomesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'bzzzz_zzzz;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, UnsignedZeroExtendOnWiden) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  initial begin\n"
      "    narrow = 4'b1010;\n"
      "    wide = narrow;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(TwoStateAndFourState, SignedSignExtendOnWiden) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] narrow;\n"
      "  logic signed [7:0] wide;\n"
      "  initial begin\n"
      "    narrow = 4'sb1111;\n"
      "    wide = narrow;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(TwoStateAndFourState, MsbTruncationOnNarrow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin\n"
      "    wide = 8'hAB;\n"
      "    narrow = wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Bu);
}

TEST(TwoStateAndFourState, LogicAndRegSimulateIdentically) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  reg [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hCA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.width, vb->value.width);
}

}  // namespace
