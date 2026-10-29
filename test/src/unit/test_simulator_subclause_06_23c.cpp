#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 with §6.7.1 and §6.22.1: a net's name is an expression of the net's
// data type, which a net declared with no data type takes as logic, so a type
// reference to the net matches logic with the net's own packed range and
// signing, and nothing else -- not bit, not another width, not the other
// signing, and not the same bits ranged the other way round (§6.22.1 (f)).
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

// §6.23 with §6.22.1: the same comparisons on variables of those types, and on
// variables of predefined-width types, whose type matches the simple vector
// of its width and signing (§6.22.1 (e)) and no other built-in type.
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

// §6.23 with §6.7.1: a net of every built-in net type declared with no data
// type is of logic, so each matches logic and none matches bit.
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

// §6.23 with §6.7.1: a net declared with a data type is of that type, integer
// matching integer and the signed 32-bit logic vector (§6.22.1 (e)) but not
// int, and a logic vector its own range but not the signed one.
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

// §6.23 with §6.6.7: a net of a user-defined nettype is of the nettype's data
// type, written out or through a typedef, which §6.22.1 (b) makes match the
// type it renames.
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

// §6.23: two type references to values compare by the values' types, so two
// nets of one type are equal and two of different types are not, by == and
// by != alike, and a net matches a variable of its type.
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

// §6.23 with §6.3.2: a drive strength or a charge strength is no part of a
// net's data type, so a net declared with one matches the type of the same
// net declared without.
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

// §6.23 with §23.2.2.3: a net port is a net of the port's data type, logic
// where the declaration writes none, with the range it writes.
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

// §6.23 with §27.5: a net or variable a generate block declares is the one a
// type reference in the block names, of the type the block declares it with,
// even where the module declares another of the name.
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

// §6.23: a comparison of type references in a continuous assignment's
// right-hand side drives the value it stands for, for a net, a variable and
// a typedef alike.
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

// §6.23 with §27.5: a comparison of type references is a constant expression,
// so it selects a generate if's branch standing alone or as an operand of a
// wider condition, and a generate case over a type reference to a net selects
// the item whose type matches the net's.
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

// §6.23 with §6.20.4: a comparison of type references is a constant
// expression, so a localparam may be set from one, standing alone or as an
// operand, and holds the value the comparison stands for.
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

// §6.23 with §6.22.1 (f): a declaration whose type is a type reference to a
// net or variable takes the value's declared type, its range as written: n's
// [0:3] keeps 0 as its left bound, which a range rebuilt from the width as
// [3:0] would not.
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
