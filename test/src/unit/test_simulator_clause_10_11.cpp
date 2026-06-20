#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

void ExpectThreeNetsAllEqual(SimFixture& f, uint64_t expected) {
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va->value.ToUint64(), expected);
  EXPECT_EQ(vb->value.ToUint64(), expected);
  EXPECT_EQ(vc->value.ToUint64(), expected);
}

TEST(NetAliasingSimulation, AliasNetsShareValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 1u);
}

TEST(NetAliasingSimulation, AliasThreeNetsShareValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectThreeNetsAllEqual(f, 1u);
}

TEST(NetAliasingSimulation, AliasMultiBitNetsShareValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] x, y;\n"
      "  alias x = y;\n"
      "  assign x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 0xABu);
  EXPECT_EQ(vy->value.ToUint64(), 0xABu);
}

TEST(NetAliasingSimulation, CumulativeAliases) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b;\n"
      "  alias b = c;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectThreeNetsAllEqual(f, 1u);
}

TEST(NetAliasingSimulation, AssignToSecondAliasedNetVisibleOnFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "  assign b = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 1u);
}

TEST(NetAliasingSimulation, AliasDoesNotAffectOtherNetBehavior) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b;\n"
      "  assign a = 1;\n"
      "  assign c = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vc->value.ToUint64(), 0u);
}

TEST(NetAliasingSimulation, AliasAmongOtherModuleItems) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, y;\n"
      "  assign y = 1;\n"
      "  alias a = b;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 1u);
  EXPECT_EQ(vy->value.ToUint64(), 1u);
}

}  // namespace
