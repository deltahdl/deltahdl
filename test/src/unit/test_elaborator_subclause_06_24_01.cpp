#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(CastOperatorElaboration, CastInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = int'(3.14);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, SignedCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = signed'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  initial void'(f());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] y;\n"
      "  assign y = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorSim, CastSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'hFF;\n"
      "    result = signed'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = -1;\n"
      "    result = unsigned'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastShortint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = 32'h1234ABCD;\n"
      "    result = shortint'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(TypeOperatorSim, TypeOpStructMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] field_a;\n"
      "    logic [7:0] field_b;\n"
      "  } my_struct;\n"
      "  my_struct s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = 16'hCAFE;\n"
      "    result = s;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(CastOperatorSim, CastConcatToShortint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint result;\n"
      "  initial result = shortint'({8'hFA, 8'hCE});\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFACEu);
}

// 6.24.1: when the casting type is a constant expression giving the target
// width, that width shall be positive. A literal zero-width size cast is an
// error.
TEST(CastOperatorElaboration, SizeCastZeroWidthLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = 0'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

// 6.24.1: the zero-or-negative size rule applies to any constant-expression
// casting type, not just a bare literal. A constant expression that folds to
// zero ((2-2)) is likewise rejected.
TEST(CastOperatorElaboration, SizeCastZeroWidthConstExprError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = (2 - 2)'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

// 6.24.1: a positive constant-expression width is the legal, accepting form of
// the size cast; it must not be flagged by the zero-or-negative-size rule.
TEST(CastOperatorElaboration, SizeCastPositiveWidthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] r;\n"
      "  initial r = 4'(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 6.24.1: the expression inside a signing cast shall be an integral value. A
// real variable driven through signed'() has no bit representation and is
// rejected.
TEST(CastOperatorElaboration, RealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = signed'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// 6.24.1: the integral-operand rule applies to unsigned'() as well as
// signed'(); a real variable inside unsigned'() is rejected.
TEST(CastOperatorElaboration, RealVarInUnsignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = unsigned'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// 6.24.1: a real literal operand is likewise non-integral, so signed'(2.5) is
// rejected -- the operand need not be a declared variable to violate the rule.
TEST(CastOperatorElaboration, RealLiteralInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    3, "6.24.1"));
}

// 6.24.1: the integral-operand rule also governs the size cast (changing the
// size), not only the signing casts. A real variable inside a numeric-width
// cast is rejected.
TEST(CastOperatorElaboration, RealVarInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expression inside a size cast shall be an integral value", 4, "6.24.1"));
}

// 6.24.1: the integral-operand rule for a size cast rejects a real *literal*
// operand as well as a real variable -- a non-integral value is illegal
// regardless of how it is written.
TEST(CastOperatorElaboration, RealLiteralInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expression inside a size cast shall be an integral value", 3, "6.24.1"));
}

// 6.24.1: shortreal is a distinct non-integral operand type; a shortreal
// variable inside a signing cast is likewise rejected by the integral-operand
// rule.
TEST(CastOperatorElaboration, ShortrealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal s;\n"
      "  int r;\n"
      "  initial r = signed'(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// §5.8: a time literal "is interpreted as a realtime value scaled to the
// current time unit", so 2.1ns is a real value and not a value of the type
// named time, which §6.11 defines as a 64-bit integral type. §6.24.1 requires
// the expression inside a signing cast to be an integral value, so
// signed'(2.1ns) breaks that rule exactly as signed'(2.5) does at
// CastOperatorElaboration.RealLiteralInSignedCastError above.
TEST(CastOperatorElaboration, TimeLiteralInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  int r;\n"
      "  initial r = signed'(2.1ns);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// §6.24.1 puts the same integral-operand rule on the size cast, and §5.8 makes
// 2.1ns a realtime value scaled to the current time unit, so 8'(2.1ns) is
// rejected too. This case reaches the operand test through the size-cast arm of
// ElaboratorOperationRules::CheckCastExpr in
// src/elaborator/elaborator_validate_operations.cpp, which reports a different
// message under the same subclause than the signing-cast arm
// CastOperatorElaboration.TimeLiteralInSignedCastError reaches.
TEST(CastOperatorElaboration, TimeLiteralInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(2.1ns);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expression inside a size cast shall be an integral value", 4, "6.24.1"));
}

TEST(CastOperatorSim, CastByteTruncate) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = byte'(32'hABCD);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// §6.24.1: "It shall be an error if the size specified is zero or negative."
// The subclause on the report is what tells this rejection from §6.24.3's
// bit-stream cast rules, which a cast naming a type rather than a width
// breaches instead.
TEST(CastOperatorElaboration, SizeCastZeroWidthNames6_24_1) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = 0'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

// §6.24.1: "If the casting type is a constant expression with a positive
// integral value, the expression in parentheses shall be padded or truncated to
// the size specified." So 4'(20) is 20 truncated to four bits: 20 is 5'b10100,
// its low four bits are 4'b0100, and the value is 4. §6.20.4 makes a
// localparam identical to a parameter but for the ways it can be overridden, so
// one holding that value is a constant expression and legal as a packed range
// bound, and `logic [W-1:0] r` with W folded to 4 is [3:0] -- four bits wide.
//
// This reads the recorded width rather than the absence of a diagnostic because
// an initializer accepted as constant and then folded to nothing reports
// nothing: the localparam is left with no value, and a case asserting the
// module elaborates cleanly passes whether the cast folded or not. A packed
// range bound has to resolve to a number before the elaborator can record a
// width, so the width it records is the value the fold produced. The three
// outcomes are distinct: 4 is the folded cast, 22 is a fold that passed the
// operand through without truncating it to four bits, and anything else is a
// range that never resolved.
TEST(CastOperatorElaboration, SizeCastInLocalparamSizesAPackedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int W = 4'(20);\n"
      "  logic [W-1:0] r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* var = FindVar(design, "m", "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->width, 4u);
}

// §6.24.1 requires the expression inside a signing cast to be an integral
// value, and names no statement the cast is allowed to stand in unjudged.
// ElaboratorOperationRules::WalkStmtsForCast in
// src/elaborator/elaborator_validate_cast_ops.cpp had written out six of the
// thirteen child-statement links Stmt declares and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The seven
// cases below are CastOperatorElaboration.RealLiteralInSignedCastError above
// rewritten in the seven positions the walk was missing, each of which
// elaborated clean beforehand with the non-integral operand unreported.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(CastOperatorElaboration, RealLiteralInSignedCastInForkArmError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial fork\n"
      "    r = signed'(2.5);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.6.2 gives `variable_assignment ::= variable_lvalue = expression`, so a cast
// stands on the right of an assignment in a for-loop header. The parser keeps
// those assignments in Stmt::for_inits.
TEST(CastOperatorElaboration, RealLiteralInSignedCastInForInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  int i;\n"
      "  initial\n"
      "    for (r = signed'(2.5); i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    5, "6.24.1"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | ...` is the same rule
// at the other end of the loop header, kept in Stmt::for_steps. The
// initializer here assigns an integer, so the report can only be about the
// step.
TEST(CastOperatorElaboration, RealLiteralInSignedCastInForStepError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; r = signed'(2.5))\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    5, "6.24.1"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  logic ok;\n"
      "  initial assert (ok) r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  logic armed;\n"
      "  initial assert (armed) else r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    4, "6.24.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §6.24.1
// judges the operand written inside the cast rather than what runs, so the
// report stands whether the weighted draw would select the item or not.
TEST(CastOperatorElaboration, RealLiteralInSignedCastInRandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial randcase 1: r = signed'(2.5); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    3, "6.24.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { r = signed'(2.5); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression inside a signing cast shall be an integral "
                    "value",
                    5, "6.24.1"));
}

}  // namespace
