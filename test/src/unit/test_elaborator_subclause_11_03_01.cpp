#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealOps, CaseEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a === b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '===' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, CaseInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !== b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '!==' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, WildcardEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '==?' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a | b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseNegOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a << 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '<<' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ModulusOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a % b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '%' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LogicalAndOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a && b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RelationalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a > b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Table 11-1 gives the binary arithmetic operators `+ - * / **` the operand
// data types "Integral, real, shortreal", so `+` on two real operands is
// admitted and the elaborator must accept this source. This is also what
// catches a change that rejects every operator while building the message
// §11.3.1 reports.
TEST(RealOps, ArithOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalEqualityOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalNegOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = !a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, UnaryPlusMinusOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial begin\n"
      "    b = +a;\n"
      "    c = -a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, WildcardInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '!=?' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, RightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '>>' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ArithLeftShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a <<< 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '<<<' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ArithRightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >>> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '>>>' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ~^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '~^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = &a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = |a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionNandOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~&a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionNorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~|a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ShortrealSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal a, b;\n"
      "  shortreal c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, RealtimeSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  realtime a, b;\n"
      "  realtime c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LogicalOrOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a || b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ConditionalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  logic sel;\n"
      "  initial c = sel ? a : b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, PowerOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a ** b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IllegalOpOnRealInContAssign) {
  ElabFixture f;
  // §6.7.1: a built-in net's data type shall be a 4-state integral type (or an
  // unpacked aggregate of such), so `wire real` is illegal independent of the
  // expression; a real-valued continuous-assignment target must be a variable
  // (§6.5/§10.3) or a user-defined nettype (§6.7.2). Using a real variable here
  // isolates the operator: the error must come from `&` applied to real
  // operands (§11.3.1), not from an illegal net declaration.
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LegalOpOnRealInContAssign) {
  ElabFixture f;
  // §6.5/§10.3: a continuous assignment may drive a variable, and a real
  // variable is a valid target (§6.7.1 forbids a real built-in net). The `+`
  // operator is legal on real operands (§11.3.1), so this elaborates cleanly.
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, InsideOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = a inside {1.0, 2.0, 3.0};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IncrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a++; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, DecrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a--; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ImplicationOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a -> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, EquivalenceOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a <-> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, StructMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { real realval; } S;\n"
      "  S s;\n"
      "  real v;\n"
      "  initial v = s.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RealArrayElementAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial begin i = 0; v = arr[i]; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §11.3.1 lists a union member alongside a structure member as a position where
// a real operand may appear. Reading a real member of an unpacked union into a
// real expression elaborates without error.
TEST(RealOps, UnionMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { real realval; longint bits; } U;\n"
      "  U u;\n"
      "  real v;\n"
      "  initial v = u.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The XNOR bitwise operator also spells as ^~, which is integral-only just like
// its ~^ form, so applying it to real operands must be rejected. The report
// echoes the spelling the source wrote, so this case expects '^~' where
// RealOps.BitwiseXnorOnRealIsIllegal expects '~^'.
TEST(RealOps, BitwiseXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^~ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^~' is not allowed on real operands", 4, "11.3.1"));
}

// The ^~ spelling of the reduction XNOR operator is likewise integral-only and
// is not permitted on a real operand. The report names the unary form, which is
// what separates this case from RealOps.BitwiseXnorCaretTildeOnRealIsIllegal.
TEST(RealOps, ReductionXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^~' is not allowed on real operands", 4, "11.3.1"));
}

// Table 11-1 bars `^~` twice, once in the row for the binary bitwise operators
// and once in the row for the unary reduction operators, so a source breaking
// both rules breaks two rules and must draw two reports that differ. This case
// writes `a ^~ b` and `^~a` into one source and names each report separately.
// Two assertions in one case is deliberate: one assertion cannot say that two
// reports differ, and that is the whole claim here. Every other case in this
// file asserts one report at line 4, so none of them can tell the two emission
// sites in Elaborator::WalkExprForRealOps apart.
TEST(RealOps, BinaryXnorAndReductionXnorGiveDifferentReports) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  logic d;\n"
      "  initial c = a ^~ b;\n"
      "  initial d = ^~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^~' is not allowed on real operands", 5, "11.3.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^~' is not allowed on real operands", 6, "11.3.1"));
}

// §11.3.1's Table 11-1 lists the operators that may have real operands, and the
// bitwise AND is not among them. WalkExprForRealOps in
// src/elaborator/elaborator_validate_operations.cpp reports one that is
// applied to a real operand, and WalkStmtsForRealOps carries that rule down a
// statement tree.
//
// That walk wrote out six of the thirteen child-statement links Stmt declares
// and now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below cover
// one newly reached position each: before the conversion `c = a & b;` was
// reported where the walk descended and accepted in every one of these seven.
//
// `stmt` is written at line 6 of the source and may run to several lines, so
// the line the report stands at is read back out of the source rather than
// counted.
void ExpectIllegalOpOnRealIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '&' is not allowed on real "
                            "operands",
                            LineHolding(src, "a & b"), "11.3.1"));
}

// §9.3.2 gives `fork { statement_or_null } join`, whose arms the parser keeps
// in Stmt::fork_stmts.
TEST(RealOps, IllegalOpOnRealInAForkArm) {
  ExpectIllegalOpOnRealIn(
      "fork\n"
      "      c = a & b;\n"
      "    join");
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, so the offending
// expression stands in a for-loop initialization, which the parser keeps in
// Stmt::for_inits.
TEST(RealOps, IllegalOpOnRealInAForInit) {
  ExpectIllegalOpOnRealIn("for (c = a & b; r == 0; r = 0) r = 1;");
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// ends in an expression, so the offending expression stands in a for-loop step,
// which the parser keeps in Stmt::for_steps.
TEST(RealOps, IllegalOpOnRealInAForStep) {
  ExpectIllegalOpOnRealIn("for (r = 0; r == 0; c = a & b) r = 1;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(RealOps, IllegalOpOnRealInAnAssertionPassStmt) {
  ExpectIllegalOpOnRealIn("assert (r) c = a & b;");
}

TEST(RealOps, IllegalOpOnRealInAnAssertionFailStmt) {
  ExpectIllegalOpOnRealIn("assert (r) else c = a & b;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §11.3.1 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(RealOps, IllegalOpOnRealInARandcaseItem) {
  ExpectIllegalOpOnRealIn("randcase 1: c = a & b; endcase");
}

// §18.17 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(RealOps, IllegalOpOnRealInARandsequenceCodeBlock) {
  ExpectIllegalOpOnRealIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { c = a & b; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
