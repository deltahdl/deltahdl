#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

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

TEST(NetAliasingSimulation, ATranReachesAcrossAnAliasOfBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire [3:0] a, b; wire c, e;\n"
                       "  alias a[3:0] = {b[0], b[1], b[2], b[3]};\n"
                       "  tran (b[0], c);\n"
                       "  assign (pull0, pull1) c = 1'b1;\n"
                       "  tran (b[1], e);\n"
                       "  assign a[2] = 1'b0;\n"
                       "  initial #1 $display(\"%v %v\", a[3], e);\n"
                       "endmodule\n",
                       f),
            "Pu1 St0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, TwoBitAliasStatementsCarryBothWays) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire [3:0] a, b, c;\n"
                       "  alias {a[1:0]} = {b[1:0]};\n"
                       "  alias {b[1:0]} = {c[1:0]};\n"
                       "  assign c[0] = 1'b1;\n"
                       "  assign a[1] = 1'b0;\n"
                       "  initial #1 $display(\"%b %b\", a[0], c[1]);\n"
                       "endmodule\n",
                       f),
            "1 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, AUdpOutputReachesAcrossAnAliasOfBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive inv(output o, input i);\n"
                       "  table 0 : 1; 1 : 0; endtable\n"
                       "endprimitive\n"
                       "module t;\n"
                       "  wire [1:0] a, b; reg r = 0, s = 1;\n"
                       "  alias a[1:0] = {b[0], b[1]};\n"
                       "  inv g(b[1], r);\n"
                       "  inv h(a[1], s);\n"
                       "  initial #1 $display(\"%v %v\", a[0], b[0]);\n"
                       "endmodule\n",
                       f),
            "St1 St0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, PullAndSupplyNetsReachAcrossAnAliasOfBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  tri1 [1:0] a0, p1; tri0 [1:0] a1, p0;\n"
                       "  supply1 [1:0] a2, s1; supply0 [1:0] a3, s0;\n"
                       "  alias a0[1:0] = {p1[0], p1[1]};\n"
                       "  alias a1 = {p0[1], p0[0]};\n"
                       "  alias a2[1:0] = {s1[0], s1[1]};\n"
                       "  alias a3 = s0;\n"
                       "  initial #1 $display(\"%v %v %v %v\", a0[0], a1[1], "
                       "a2[0], a3[1]);\n"
                       "endmodule\n",
                       f),
            "Pu1 Pu0 Su1 Su0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, ATriregChargeReachesAcrossAnAliasOfBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  trireg [1:0] a, b; reg en = 1;\n"
                       "  alias a[1:0] = {b[0], b[1]};\n"
                       "  bufif1 (b[1], 1'b1, en);\n"
                       "  initial begin #5 en = 0; #5 $display(\"%v\", a[0]); "
                       "end\n"
                       "endmodule\n",
                       f),
            "Me1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, ADelayedDriverLeavesXAcrossAnAliasOfBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire [1:0] a, b;\n"
                       "  alias a[1:0] = {b[0], b[1]};\n"
                       "  assign #5 b = 2'b11;\n"
                       "  initial begin #1 $display(\"%v\", a[0]); #5 "
                       "$display(\"%v\", a[0]); end\n"
                       "endmodule\n",
                       f),
            "StX\nSt1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, ImplicitAliasNetsCarryEitherWay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire a; alias a = b;\n"
                       "  assign a = 1'b1;\n"
                       "  wire c; alias c = d = e;\n"
                       "  assign e = 1'b0;\n"
                       "  initial #1 $display(\"%b %b %b\", b, c, d);\n"
                       "endmodule\n",
                       f),
            "1 0 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation,
     DISABLED_ImplicitNetsOfAConcatenationOperandJoinTheBits) {
  for (const char* src : {"module t;\n"
                          "  wire [1:0] a; alias a = {b, c};\n"
                          "  assign a = 2'b10;\n"
                          "  initial #1 $display(\"%b %b\", b, c);\n"
                          "endmodule\n",
                          "module t;\n"
                          "  if (1) begin : g\n"
                          "    wire [1:0] a; alias a = {b, c};\n"
                          "    assign a = 2'b10;\n"
                          "  end\n"
                          "  initial #1 $display(\"%b %b\", g.b, g.c);\n"
                          "endmodule\n",
                          "interface I;\n"
                          "  wire [1:0] a; alias a = {b, c};\n"
                          "  assign a = 2'b10;\n"
                          "endinterface\n"
                          "module t;\n"
                          "  I u();\n"
                          "  initial #1 $display(\"%b %b\", u.b, u.c);\n"
                          "endmodule\n"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "1 0\n") << src;
    EXPECT_FALSE(f.diag.HasErrors()) << src;
  }
}

TEST(NetAliasingSimulation, AnInterfaceAliasJoinsEachInstancesNets) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus; wire a, b; alias a = b; endinterface\n"
                       "module t;\n"
                       "  bus u(); bus v();\n"
                       "  assign u.a = 1'b1;\n"
                       "  assign v.b = 1'b0;\n"
                       "  initial #1 $display(\"%b %b %b %b\", u.a, u.b, v.a, "
                       "v.b);\n"
                       "endmodule\n",
                       f),
            "1 1 0 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation, AliasesInAnInterfacesGenerateBlocks) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface bus #(parameter N = 2);\n"
                 "  wire a, b, c, d;\n"
                 "  if (N > 1) begin : g alias a = b; end\n"
                 "  for (genvar i = 0; i < 1; i++) begin : l alias c = d; "
                 "end\n"
                 "  assign b = 1; assign c = 0;\n"
                 "endinterface\n"
                 "module t; bus u(); initial #1 $display(\"%b %b\", u.a, "
                 "u.d); endmodule\n",
                 f),
      "1 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingSimulation,
     DISABLED_AnInterfaceAliasOfAPortNetReachesTheConnectedNet) {
  for (const auto& [src, expected] :
       {std::pair{"interface bus(inout wire p);\n"
                  "  wire q; alias p = q; assign q = 1'b1;\n"
                  "endinterface\n"
                  "module t; wire n; bus u(n); initial #1 $display(\"%b\", "
                  "n); endmodule\n",
                  "1\n"},
        std::pair{"interface bus(inout wire [1:0] p);\n"
                  "  wire [1:0] q; alias p = q; assign q = 2'b10;\n"
                  "endinterface\n"
                  "module t; wire [1:0] n; bus u(n); initial #1 "
                  "$display(\"%b\", n); endmodule\n",
                  "10\n"}}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), expected) << src;
    EXPECT_FALSE(f.diag.HasErrors()) << src;
  }
}

}  // namespace
