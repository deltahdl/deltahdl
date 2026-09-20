#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ConstEval, BitsExpr) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
}

// §20.6.2 (NC5): $bits on a fixed-size built-in data type folds to an
// elaboration-time constant. A bare type keyword contributes its atom width and
// a ranged vector its full packed width — resolved purely by const evaluation,
// with nothing run. This is the data_type argument form of the BNF.
TEST(ConstEval, BitsOfBuiltinDataTypeFolds) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(int)", f)), 32);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(byte)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(logic [7:0])", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(logic [31:0])", f)), 32);
}

// §20.6.2: the result is fixed by the inner expression's declared width
// alone; the value content is never actually evaluated. A literal whose
// digits are entirely x is uninterpretable as a number, yet $bits still
// returns its declared 12-bit width at elaboration time.
TEST(ConstEval, BitsLiteralIsResolvedWithoutEvaluatingValue) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(12'bxxxxxxxxxxxx)", f)), 12);
}

// §20.6.2: applying $bits directly to a dynamically sized type identifier
// (queue typedef here) has no defined extent and shall be an error.
TEST(BitsCallRestrictions, BitsOnQueueTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial n = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 4,
      "20.6.2"));
}

// §20.6.2: the same restriction covers a dynamically sized type spelled as a
// dynamic array (byte dt[]), not only a queue — applying $bits directly to the
// type identifier has no defined extent and shall be an error.
TEST(BitsCallRestrictions, BitsOnDynamicArrayTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte dt[];\n"
      "  int n;\n"
      "  initial n = $bits(dt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'dt'", 4,
      "20.6.2"));
}

// §20.6.2: because $bits folds to an elaboration-time constant for a
// fixed-size argument, it may appear inside the packed dimension of a data
// type declaration, and the resulting typedef shall elaborate cleanly.
TEST(BitsCallRestrictions, BitsResultUsableInDataTypeDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef bit [$bits(16'h0):1] MyBits;\n"
      "  MyBits b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.6.2 (NC5): the elaboration-time constant that $bits folds to on a
// fixed-size argument may appear in the packed dimension of a plain variable
// declaration, not just a typedef. The variable shall elaborate cleanly.
TEST(BitsCallRestrictions, BitsResultUsableInVariableDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  bit [$bits(16'h0):1] v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.6.2 (NC5): the same elaboration-time constant may size a net
// declaration. A wire whose width is derived from $bits shall elaborate
// cleanly.
TEST(BitsCallRestrictions, BitsResultUsableInNetDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [$bits(16'h0):1] w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.6.2: the same query on a fixed-size type identifier is legal.
TEST(BitsCallRestrictions, BitsOnFixedTypedefIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef logic [3:0] ft;\n"
      "  int n;\n"
      "  initial n = $bits(ft);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.6.2: $bits shall not enclose a function whose return type is a
// dynamically sized data type.
TEST(BitsCallRestrictions, BitsEnclosingDynamicReturnFuncIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  function qt mkq(); return mkq; endfunction\n"
      "  int n;\n"
      "  initial n = $bits(mkq());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$bits' shall not enclose function 'mkq' whose "
                            "return type is dynamically sized",
                            5, "20.6.2"));
}

// §20.6.2 (with §8.26 satisfied): $bits shall not be applied to an object
// whose type is an interface class.
TEST(BitsCallRestrictions, BitsOnInterfaceClassObjectIsError) {
  ElabFixture f;
  Elaborate(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC h;\n"
      "  int n;\n"
      "  initial n = $bits(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' shall not be applied to interface class object 'h'", 7,
      "20.6.2"));
}

// §20.6.2 says "It shall be an error to: -- Use the $bits system function
// directly with a dynamically sized data type identifier", and states no
// condition on where the call stands. So the error is owed wherever a statement
// can be written, and the five cases below each put the call in one statement
// position of a module whose 'qt' is a queue typedef.
//
// Each of those five is a position
// Elaborator::ValidateBitsCallRestrictions reached only once CheckBitsCallStmt
// in src/elaborator/elaborator_validate_queries_dims.cpp took its list of
// nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, leaving a $bits applied to a type with no defined extent
// unreported.

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and A.6.2's
// operator_assignment is `variable_lvalue assignment_operator expression`, so
// the loop's third header clause holds a statement of its own, kept in
// Stmt::for_steps. The initializer here assigns a constant, so the report can
// only name the call in the step.
TEST(BitsCallRestrictions, BitsOnQueueTypedefInAForStepIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; n = $bits(qt))\n"
      "      n = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 6,
      "20.6.2"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(BitsCallRestrictions,
     BitsOnQueueTypedefInAnAssertionPassStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  logic ok;\n"
      "  initial assert (ok) n = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 5,
      "20.6.2"));
}

TEST(BitsCallRestrictions,
     BitsOnQueueTypedefInAnAssertionFailStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int c;\n"
      "  logic pass;\n"
      "  initial assert (pass) else c = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 5,
      "20.6.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §20.6.2's
// error is a static one, so it stands whether the weighted draw would select
// the item or not.
TEST(BitsCallRestrictions, BitsOnQueueTypedefInARandcaseItemIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int total;\n"
      "  initial randcase 1: total = $bits(qt); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 4,
      "20.6.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(BitsCallRestrictions, BitsOnQueueTypedefInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int width;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { width = $bits(qt); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 6,
      "20.6.2"));
}

// §20.6.2 (printed page 629) has $bits answer the number of bits an
// expression holds and lets a fixed-size answer stand as an elaboration-time
// constant, and §6.20.2 (printed page 126) gives a parameter declared with a
// range the range of its declaration. So $bits of a parameter declared
// `logic [95:0]` is 96, and a localparam set to it resolves at elaboration
// with that value, where a fold that sized literals and type keywords alone
// left the localparam with no value at all -- is_resolved false on its
// declaration.
TEST(BitsOfDeclaration, RangedParameterAnswersItsDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int W = $bits(P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 96);
}

// §6.20.2 (printed page 126): a parameter declared with a type and no range is
// of that type, so `localparam int N = 5` holds int's 32 bits whatever its
// value needs -- 5 fits in 3 bits, which is the answer a fold sizing the value
// rather than the declaration would give.
TEST(BitsOfDeclaration, TypedParameterAnswersItsTypeWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int N = 5;\n"
      "  localparam int BN = $bits(N);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bn = FindParam(design, "m", "BN");
  ASSERT_NE(bn, nullptr);
  EXPECT_TRUE(bn->is_resolved);
  EXPECT_EQ(bn->resolved_value, 32);
}

// §6.20.2 (printed page 127): a parameter declared with neither type nor range
// takes an implied range from the size of the final value assigned to it, and
// at least 32 bits when that value is unsized. The clause's own examples set
// `newconst = 3'h4` to [2:0] and `newconst = 4` to at least [31:0], so a sized
// literal of 8 bits gives 8 and an unsized decimal gives 32.
TEST(BitsOfDeclaration, ImplicitParameterAnswersItsValueWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam Q = 8'hFF;\n"
      "  localparam R = 100;\n"
      "  localparam int BQ = $bits(Q);\n"
      "  localparam int BR = $bits(R);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bq = FindParam(design, "m", "BQ");
  ASSERT_NE(bq, nullptr);
  EXPECT_TRUE(bq->is_resolved);
  EXPECT_EQ(bq->resolved_value, 8);
  const auto* br = FindParam(design, "m", "BR");
  ASSERT_NE(br, nullptr);
  EXPECT_TRUE(br->is_resolved);
  EXPECT_EQ(br->resolved_value, 32);
}

// §20.6.2 (printed page 629) lets the constant $bits folds to size the
// declaration of another variable, its own example being a typedef of
// `bit [$bits(MyType):1]`. A variable whose packed range is written in terms
// of $bits of a 96-bit parameter is 96 bits wide, and not the 1 bit a range
// with an unfolded bound falls back to.
TEST(BitsOfDeclaration, ParameterWidthSizesAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  logic [$bits(P)-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 96u);
}

// §20.6.2 (printed page 629) opens with `logic [31:0] v` and has $bits(v)
// answer 32, the bits the declaration gives the variable. A variable the
// module has already elaborated carries that width, so a localparam set to
// $bits of a 16-bit variable resolves to 16 at elaboration.
TEST(BitsOfDeclaration, VariableAnswersItsDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  localparam int BX = $bits(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bx = FindParam(design, "m", "BX");
  ASSERT_NE(bx, nullptr);
  EXPECT_TRUE(bx->is_resolved);
  EXPECT_EQ(bx->resolved_value, 16);
}

}  // namespace
