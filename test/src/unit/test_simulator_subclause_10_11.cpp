#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

// §10.11 in an instantiated module: an alias statement makes its nets one
// physical net, and §23.9 resolves the bare names it writes in the module
// that declares them, so each instance of M has its own a and b joined. The
// lowerer registered a top's alias alone; an instance's was never lowered,
// so m1.b and m2.b were created under their instance prefixes and left
// undriven, both reading z, which ToUint64 collapses to 0. Each instance's
// b now reads what its own a is driven to: m1.b 4'b1010 and m2.b 4'b0101.
TEST(NetAliasingSimulation, EachInstanceAliasBindsItsOwnNets) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M(input logic i);\n"
      "  wire [3:0] a, b;\n"
      "  alias a = b;\n"
      "  assign a = {i, ~i, i, ~i};\n"
      "endmodule\n"
      "module top;\n"
      "  logic p, q;\n"
      "  M m1(.i(p));\n"
      "  M m2(.i(q));\n"
      "  initial begin\n"
      "    p = 1;\n"
      "    q = 0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("m1.b");
  auto* b2 = f.ctx.FindVariable("m2.b");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 0xAu);
  EXPECT_EQ(b2->value.ToUint64(), 0x5u);
}

// §23.9: the alias M writes names M's own nets, so the top's like-named a
// and b, which no alias joins, stay two nets. The top's b is undriven and
// reads z, collapsed to 0, while m.b reads the 1 m.a is driven to.
TEST(NetAliasingSimulation, ChildAliasLeavesTheTopsLikeNamedNetsApart) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = 1'b1;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* top_b = f.ctx.FindVariable("b");
  auto* child_b = f.ctx.FindVariable("m.b");
  ASSERT_NE(top_b, nullptr);
  ASSERT_NE(child_b, nullptr);
  EXPECT_EQ(top_b->value.ToUint64(), 0u);
  EXPECT_EQ(child_b->value.ToUint64(), 1u);
}

// §10.11's byte_swap example: an alias operand may be a concatenation of
// part-selects, and the bits the two sides list are joined in order, so B is
// the byte-swapped A. Joined whole net to whole net, the concatenation named
// no net and B was left at z.
TEST(NetAliasingSimulation, ByteSwapAliasOfPartSelects) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  wire [31:0] A, B; logic [31:0] drv;\n"
      "  assign A = drv;\n"
      "  alias {A[7:0], A[15:8], A[23:16], A[31:24]} = B;\n"
      "  initial begin drv = 32'h12345678; #1 $display(\"%h %h\", A, B); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12345678 78563412\n");
}

// The join carries a value whichever side is driven: driving the whole net on
// the right reaches the nets the concatenation on the left lists, and a later
// change of it reaches them again.
TEST(NetAliasingSimulation, PartSelectAliasCarriesTheOtherWay) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  wire [7:0] lo, hi; wire [15:0] w; logic [15:0] d;\n"
      "  assign w = d;\n"
      "  alias {hi, lo} = w;\n"
      "  initial begin\n"
      "    d = 16'hABCD; #1 $display(\"%h %h\", hi, lo);\n"
      "    d = 16'h0102; #1 $display(\"%h %h\", hi, lo);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ab cd\n01 02\n");
}

}  // namespace
