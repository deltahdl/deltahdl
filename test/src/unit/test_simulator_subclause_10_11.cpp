#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

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

TEST(NetAliasingSimulation, TwoStatementsSharingANetJoinAllThree) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b;\n"
      "  alias c = b;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ExpectThreeNetsAllEqual(f, 1);
}

TEST(NetAliasingSimulation, AnAliasInAGenerateBlockJoinsTheBlocksNets) {
  const char* src =
      "module m;\n"
      "  wire o;\n"
      "  logic r1, r2;\n"
      "  if (1) begin : g\n"
      "    wire a, b;\n"
      "    alias a = b;\n"
      "    assign a = 1'b1;\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    wire p;\n"
      "    alias p = o;\n"
      "    assign p = 1'b1;\n"
      "  end\n"
      "  initial #1 begin r1 = g.b; r2 = o; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r1"), 1u);
  EXPECT_EQ(RunAndGet(src, "r2"), 1u);
}

TEST(NetAliasingSimulation, APatternOperandJoinsItsItemsBitsInOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "module t;\n"
      "  wire [7:0] w, v; wire [3:0] a, b, c, d; logic [7:0] dw, dv;\n"
      "  assign w = dw;\n"
      "  assign v = dv;\n"
      "  alias w = pair_t'{a, b};\n"
      "  alias v = '{c, d};\n"
      "  initial begin\n"
      "    dw = 8'h5C; dv = 8'h3E;\n"
      "    #1 $display(\"%h %h %h %h\", a, b, c, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 c 3 e\n");
}

}  // namespace
