#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.4.4.1: the operands of a state-dependent path conditional expression may
// be input/inout ports (or their selects), locally defined nets/variables, or
// compile-time constants (specparams, literals). This bundles an input port, a
// local net, and a specparam under the logical-AND operator -- all permitted --
// so elaboration must accept it.
TEST(OperatorElaboration, ModulePathOperandClassesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    specparam SP = 1;\n"
      "    if (a && en && SP) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: a locally defined variable (not just a net) is an allowed operand.
TEST(OperatorElaboration, LocalVariableOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  logic gate;\n"
      "  specify\n"
      "    if (gate) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: a part-select of an input port is an allowed operand (the
// bit-select form is covered separately).
TEST(OperatorElaboration, PartSelectOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[1:0]) (a[0] => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: an inout port is an allowed operand.
TEST(OperatorElaboration, InoutPortOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, inout b, output y);\n"
      "  specify\n"
      "    if (b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: a bit-select of an input port and a constant number are allowed
// operands.
TEST(OperatorElaboration, BitSelectAndConstantOperandsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[0] && 1'b1) (a[0] => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: reduction, bitwise, and conditional (?:) operators are
// all valid in a conditional expression, so a combination of them elaborates.
// This bundle exercises reduction AND (~&), reduction XOR (^), bitwise OR (|),
// reduction AND (&), and the conditional operator (?:).
TEST(OperatorElaboration, TableOperatorsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, input sel, output y);\n"
      "  specify\n"
      "    if (sel ? (~&a) : (^a | &a)) (a[0] => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: bitwise negation (~) is a valid operator. Each Table
// 30-1 operator is a distinct branch of the elaboration allow-set, so it is
// exercised individually at the stage where the restriction applies.
TEST(OperatorElaboration, BitwiseNegationOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: logical negation (!) is a valid operator.
TEST(OperatorElaboration, LogicalNotOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: logical equality (==) is a valid operator.
TEST(OperatorElaboration, LogicalEqualityOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: logical inequality (!=) is a valid operator.
TEST(OperatorElaboration, LogicalInequalityOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: logical OR (||) is a valid operator.
TEST(OperatorElaboration, LogicalOrOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: bitwise XNOR (^~) is a valid operator.
TEST(OperatorElaboration, BitwiseXnorOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: the alternate XNOR spelling (~^) is also valid -- it
// is a distinct token from ^~, so it takes its own branch of the allow-set.
TEST(OperatorElaboration, BitwiseXnorAltOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ~^ b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: reduction NOR (~|) is a valid operator.
TEST(OperatorElaboration, ReductionNorOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (~|a) (a[0] => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: a concatenation ({}) is a valid conditional-expression
// element; the operand check descends into its members.
TEST(OperatorElaboration, ConcatenationOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if ({a, b}) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1, Table 30-1: a replication ({{}}) is a valid conditional-expression
// element.
TEST(OperatorElaboration, ReplicationOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if ({2{a}}) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: an output port is not an allowed operand of a conditional
// expression (only input and inout ports are). Using the destination output as
// a condition operand must be rejected.
TEST(OperatorElaboration, OutputPortOperandIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (y) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1: the output-port prohibition applies to a select of an output port
// too, not just the whole port -- the check descends into the bit-/part-select
// to reach the underlying signal.
TEST(OperatorElaboration, OutputPortBitSelectOperandIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output [3:0] y);\n"
      "  specify\n"
      "    if (y[0]) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: an arithmetic operator is not among the valid
// conditional-expression operators and must be rejected. Both operands (an
// input port and a local net) are otherwise legal, so the sole error is the
// '+' operator.
TEST(OperatorElaboration, ArithmeticOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a + en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: relational operators are excluded.
TEST(OperatorElaboration, RelationalOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a > en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: shift operators are excluded.
TEST(OperatorElaboration, ShiftOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (a << 1) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: only logical equality (==) and inequality (!=) are
// valid; case equality (===) is not.
TEST(OperatorElaboration, CaseEqualityOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a === en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: the power operator (**) is not a valid conditional-
// expression operator and must be rejected.
TEST(OperatorElaboration, PowerOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ** b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1, Table 30-1: the restriction applies to unary operators too. A
// unary arithmetic operator (unary +) is not in the table and must be rejected
// -- this exercises the unary branch of the check, distinct from the binary
// rejections above.
TEST(OperatorElaboration, UnaryArithmeticOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (+a) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1: the operand and operator rules are enforced on the whole tree, not
// just its root -- a disallowed operator nested beneath a permitted one is
// still rejected.
TEST(OperatorElaboration, NestedDisallowedOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (en || (a - en)) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.4.1: the conditional expression governs a state-dependent path whether
// the path is a simple path or an edge-sensitive path (§30.4.3). Built from a
// real edge-sensitive path, a permitted operand (a local net) still elaborates
// -- the operand rule applies at this syntactic position.
TEST(OperatorElaboration, ConditionOnEdgeSensitivePathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input a, output q);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.1: the operand rule fires on the condition of an edge-sensitive path
// too -- an output port used as an operand is rejected regardless of the path
// form the condition guards (§30.4.3 syntactic position).
TEST(OperatorElaboration, OutputOperandOnEdgeSensitivePathIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input a, output q);\n"
      "  specify\n"
      "    if (q) (posedge clk => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
