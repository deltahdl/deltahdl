#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypeOfValueCompareSim, NetMatchesItsImplicitLogicType) {
  const std::string kSrc =
      "module t;\n"
      "  wire n;\n"
      "  wire [3:0] v;\n"
      "  wire signed [3:0] s;\n"
      "  wire [0:3] a;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(n) == type(logic), type(n) == type(bit),\n"
      "         type(v) == type(logic [3:0]), type(v) == type(logic [4:0]),\n"
      "         type(s) == type(logic signed [3:0]),\n"
      "         type(s) == type(logic [3:0]),\n"
      "         type(a) == type(logic [0:3]), type(a) == type(logic [3:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10101010u);
}

TEST(TypeOfValueCompareSim, VariableMatchesItsDeclaredType) {
  const std::string kSrc =
      "module t;\n"
      "  logic n;\n"
      "  logic [3:0] v;\n"
      "  logic signed [3:0] s;\n"
      "  logic [0:3] a;\n"
      "  int i;\n"
      "  integer g;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(n) == type(logic), type(n) == type(bit),\n"
      "         type(v) == type(logic [3:0]), type(v) == type(logic [4:0]),\n"
      "         type(s) == type(logic signed [3:0]),\n"
      "         type(s) == type(logic [3:0]),\n"
      "         type(a) == type(logic [0:3]), type(a) == type(logic [3:0]),\n"
      "         type(i) == type(int), type(i) == type(bit signed [31:0]),\n"
      "         type(i) == type(integer), type(g) == type(integer),\n"
      "         type(g) == type(int)};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1010101011010u);
}

TEST(TypeOfValueCompareSim, NetOfEveryBuiltInNetTypeMatchesLogic) {
  const std::string kSrc =
      "module t;\n"
      "  tri n0;\n"
      "  wand n1;\n"
      "  wor n2;\n"
      "  triand n3;\n"
      "  trior n4;\n"
      "  tri0 n5;\n"
      "  tri1 n6;\n"
      "  trireg n7;\n"
      "  uwire n8;\n"
      "  supply0 n9;\n"
      "  supply1 n10;\n"
      "  int r, s;\n"
      "  initial begin\n"
      "    r = {type(n0) == type(logic), type(n1) == type(logic),\n"
      "         type(n2) == type(logic), type(n3) == type(logic),\n"
      "         type(n4) == type(logic), type(n5) == type(logic),\n"
      "         type(n6) == type(logic), type(n7) == type(logic),\n"
      "         type(n8) == type(logic), type(n9) == type(logic),\n"
      "         type(n10) == type(logic)};\n"
      "    s = {type(n0) == type(bit), type(n3) == type(bit),\n"
      "         type(n7) == type(bit), type(n8) == type(bit),\n"
      "         type(n10) == type(bit)};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0x7FFu);
  EXPECT_EQ(RunAndGet(kSrc, "s"), 0u);
}

TEST(TypeOfValueCompareSim, NetMatchesTheDataTypeItsDeclarationWrites) {
  const std::string kSrc =
      "module t;\n"
      "  wire integer wi;\n"
      "  wire logic [7:0] wl;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(wi) == type(integer), type(wi) == type(int),\n"
      "         type(wi) == type(logic signed [31:0]),\n"
      "         type(wl) == type(logic [7:0]),\n"
      "         type(wl) == type(logic signed [7:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10110u);
}

TEST(TypeOfValueCompareSim, NetOfAUserNettypeMatchesTheNettypesDataType) {
  const std::string kSrc =
      "module t;\n"
      "  typedef logic [2:0] tri_t;\n"
      "  nettype logic [1:0] nt;\n"
      "  nettype tri_t nt3;\n"
      "  nt n;\n"
      "  nt3 m;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(n) == type(logic [1:0]), type(n) == type(logic [2:0]),\n"
      "         type(m) == type(tri_t), type(m) == type(logic [2:0]),\n"
      "         type(m) == type(logic [1:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10110u);
}

TEST(TypeOfValueCompareSim, TwoValuesCompareByTheirTypes) {
  const std::string kSrc =
      "module t;\n"
      "  wire [3:0] a, b;\n"
      "  wire [4:0] c;\n"
      "  logic [3:0] lv;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(a) == type(b), type(a) == type(c), type(a) != type(c),\n"
      "         type(a) != type(b), type(a) === type(lv),\n"
      "         type(c) !== type(lv)};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b101011u);
}

TEST(TypeOfValueCompareSim, StrengthIsNoPartOfANetsType) {
  const std::string kSrc =
      "module t;\n"
      "  logic a;\n"
      "  wire (strong0, weak1) w = a;\n"
      "  trireg (large) c;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(w) == type(logic), type(c) == type(logic),\n"
      "         type(cap2) == type(logic signed [3:0]),\n"
      "         type(cap2) == type(logic [3:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1110u);
}

TEST(TypeOfValueCompareSim, NetPortMatchesItsDeclaredType) {
  const std::string kSrc =
      "module t(input wire [0:3] p, input [2:0] q);\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(p) == type(logic [0:3]), type(p) == type(logic [3:0]),\n"
      "         type(q) == type(logic [2:0]), type(q) == type(bit [2:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1010u);
}

TEST(TypeOfValueCompareSim, ValueOfAGenerateBlockIsTypedInTheBlock) {
  const std::string kSrc =
      "module t;\n"
      "  wire [7:0] n;\n"
      "  int r;\n"
      "  if (1) begin : g\n"
      "    wire [0:3] n;\n"
      "    logic signed [2:0] v;\n"
      "    initial r = {type(n) == type(logic [0:3]),\n"
      "                 type(n) == type(logic [7:0]),\n"
      "                 type(v) == type(logic signed [2:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b101u);
}

TEST(TypeOfValueCompareSim, ComparisonInAContinuousAssignment) {
  const std::string kSrc =
      "module t;\n"
      "  typedef bit node;\n"
      "  wire [3:0] n;\n"
      "  logic [0:3] v;\n"
      "  logic [5:0] r;\n"
      "  assign r = {type(n) == type(logic [3:0]),\n"
      "              type(n) == type(logic [4:0]),\n"
      "              type(v) == type(logic [0:3]),\n"
      "              type(v) == type(logic [3:0]),\n"
      "              type(node) == type(bit), type(node) == type(logic)};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b101010u);
}

TEST(TypeOfValueCompareSim, ComparisonSelectsAGenerateBranch) {
  const std::string kSrc =
      "module t;\n"
      "  wire [3:0] n;\n"
      "  logic [0:3] v;\n"
      "  int r, s, c;\n"
      "  if (type(n) == type(logic [3:0])) begin : a\n"
      "    initial r = 1;\n"
      "  end else begin : b\n"
      "    initial r = 2;\n"
      "  end\n"
      "  if (type(v) == type(logic [3:0]) || 0) begin : d\n"
      "    initial s = 1;\n"
      "  end else begin : e\n"
      "    initial s = 2;\n"
      "  end\n"
      "  case (type(n))\n"
      "    type(logic [4:0]): begin : f initial c = 1; end\n"
      "    type(logic [3:0]): begin : g initial c = 2; end\n"
      "    default: begin : h initial c = 3; end\n"
      "  endcase\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "s"), 2u);
  EXPECT_EQ(RunAndGet(kSrc, "c"), 2u);
}

TEST(TypeOfValueCompareSim, ComparisonSetsAParameter) {
  const std::string kSrc =
      "module t;\n"
      "  typedef bit node;\n"
      "  wire [3:0] n;\n"
      "  logic [0:3] v;\n"
      "  localparam bit P = type(n) == type(logic [3:0]);\n"
      "  localparam bit Q = type(n) == type(logic [4:0]);\n"
      "  localparam bit R = type(v) != type(logic [3:0]);\n"
      "  localparam bit S = type(node) == type(bit) && P;\n"
      "  localparam int T = (type(v) == type(logic [0:3])) ? 7 : 9;\n"
      "  int r;\n"
      "  initial r = {P, Q, R, S, T[3:0]};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10110111u);
}

TEST(TypeOfValueCompareSim, DeclarationTakesAValuesDeclaredRange) {
  const std::string kSrc =
      "module t;\n"
      "  wire [0:3] n;\n"
      "  logic [1:4] lv;\n"
      "  var type(n) a;\n"
      "  wire type(n) b;\n"
      "  var type(lv) c;\n"
      "  int r;\n"
      "  initial r = {4'($left(a)), 4'($right(a)), 4'($left(b)),\n"
      "               4'($right(b)), 4'($left(c)), 4'($right(c))};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0x030314u);
}

}  // namespace
