#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"
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

// §5.7.1 (printed page 78) with §20.6.2: an unbased unsized literal is one
// bit wide in a self-determined context, and $bits's argument is one, so
// `$bits('1)` and `$bits('x)` fold to 1. The fold had no width for the
// literal and declined.
TEST(ConstEval, BitsOfUnbasedUnsizedLiteralIsOne) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits('1)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits('x)", f)), 1);
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

// §6.20.2 (printed page 126): a parameter declared with neither type nor range
// takes the size of its final value, and a name standing for a 96-bit
// parameter is 96 bits wide, so `localparam S = P` holds 96 bits and $bits(S)
// answers 96 -- not the 32 of a fold that read every name as an int.
TEST(BitsOfDeclaration, ImplicitParameterSetFromAWideParameterIsAsWide) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam S = P;\n"
      "  localparam int BS = $bits(S);\n"
      "  localparam int SH = S[95:64];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BS"), 96);
  EXPECT_EQ(ParamValue(design, "SH"), 0x01234567);
}

// §11.6.1's Table 11-21 (printed pages 299-300) sizes a self-determined
// expression by its operator: the arithmetic and bitwise operators take the
// wider operand, a shift and a power the left operand, a comparison, an
// equality, a logical operator, an implication, a reduction and `!` one bit,
// unary `+ - ~` their operand, a conditional the wider arm. B is 8 bits and
// an unsized literal at least 32, so `B + B` is 8 bits and `B + 1` is 32.
TEST(BitsOfDeclaration, OperatorExpressionIsSizedByTable11_21) {
  const std::vector<std::pair<std::string, int64_t>> kCases{
      {"B + B", 8},   {"B - B", 8},   {"B * B", 8},
      {"B / B", 8},   {"B % B", 8},   {"B & B", 8},
      {"B | B", 8},   {"B ^ B", 8},   {"B ^~ B", 8},
      {"B ~^ B", 8},  {"B + 1", 32},  {"B << 4", 8},
      {"B <<< 4", 8}, {"B >> 4", 8},  {"B >>> 4", 8},
      {"B ** 2", 8},  {"B < B", 1},   {"B > B", 1},
      {"B <= B", 1},  {"B >= B", 1},  {"B == B", 1},
      {"B != B", 1},  {"B === B", 1}, {"B !== B", 1},
      {"B ==? B", 1}, {"B !=? B", 1}, {"B && B", 1},
      {"B || B", 1},  {"B -> B", 1},  {"B <-> B", 1},
      {"+B", 8},      {"-B", 8},      {"~B", 8},
      {"&B", 1},      {"~&B", 1},     {"|B", 1},
      {"~|B", 1},     {"^B", 1},      {"~^B", 1},
      {"^~B", 1},     {"!B", 1},      {"B ? B : 16'h1", 16}};
  std::string src =
      "module m;\n"
      "  localparam logic [7:0] B = 8'hFF;\n";
  for (size_t i = 0; i < kCases.size(); ++i) {
    src += "  localparam int W" + std::to_string(i) + " = $bits(" +
           kCases[i].first + ");\n";
  }
  src += "endmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (size_t i = 0; i < kCases.size(); ++i) {
    EXPECT_EQ(ParamValue(design, "W" + std::to_string(i)), kCases[i].second)
        << kCases[i].first;
  }
}

// A binary operator Table 11-21 does not size -- the sequence implication,
// which makes no expression at all -- leaves $bits unfolded rather than sized
// as something it is not.
TEST(BitsOfDeclaration, OperatorOutsideTable11_21IsLeftUnsized) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [7:0] B = 8'hFF;\n"
      "  localparam int W = $bits(B |-> B);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(design == nullptr || ParamUnresolved(design, "W"));
}

// §6.20.2 (printed page 127): a parameter declared with a type keeps the
// width and signedness of that type whatever value it was set to, so a byte
// set to 300 is read as the 44 the low eight bits hold and a 4-bit unsigned
// vector set to -1 as 15. One with a bare `signed` and no range takes the
// range of its value, so SG is the 32-bit -3 it was set to.
TEST(BitsOfDeclaration, ParameterNameReadsAtItsDeclaredWidthAndSign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte B = 300;\n"
      "  localparam bit [3:0] Y = -1;\n"
      "  parameter signed SG = -3;\n"
      "  localparam int RB = B;\n"
      "  localparam int RY = Y;\n"
      "  localparam int RS = SG;\n"
      "  localparam int BSG = $bits(SG);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "RB"), 44);
  EXPECT_EQ(ParamValue(design, "RY"), 15);
  EXPECT_EQ(ParamValue(design, "RS"), -3);
  EXPECT_EQ(ParamValue(design, "BSG"), 32);
}

// §13.4.3 folds a constant function's body against its locals, which sit in
// the same scope map as the module's parameters under bare names. A formal
// named as a byte parameter is holds the 300 the call passed, not the 44 the
// parameter's width would leave, so the declaration is applied only to a name
// whose value is the parameter's.
TEST(BitsOfDeclaration, FormalNamedAsAParameterIsNotCutToItsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte K = 3;\n"
      "  function automatic int f(input int K);\n"
      "    return K;\n"
      "  endfunction\n"
      "  localparam int R = f(300);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "R"), 300);
}

// §6.20.2: a parameter with neither type nor range whose value is an
// enumeration constant (§6.19) takes the value's size, and the constant is not
// among the module's parameters the fold sizes it against, so the name reads
// as a 32-bit signed integer, as every name did before.
TEST(BitsOfDeclaration, ImplicitParameterSetFromAnEnumConstantReadsAsInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {A0, A1} e_t;\n"
      "  localparam E = A1;\n"
      "  localparam int X = E + A1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "X"), 2);
}

// §23.9 has a module's own P hide the compilation unit's inside the module,
// so a value written as `P + 1` names the parameter it initializes, which
// §6.20.1 does not admit; the elaborator folded it against the unit's P
// before this and still does. Sizing a later read of P folds `P + 1` again,
// which names P again, and the fold is capped rather than run without end:
// elaboration terminates and H reads the low word alone.
TEST(BitsOfDeclaration, SelfReferentialWideParameterTerminates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "localparam logic [95:0] P = 96'h1;\n"
      "module m;\n"
      "  localparam logic [95:0] P = P + 1;\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "H"), 0);
  EXPECT_EQ(ParamValue(design, "L"), 2);
}

// §5.7.1 (printed page 77): a based literal's digits give its value in the
// base its base format character names, in either case, with x ending the
// digits the fold reads, and the size constant states the width the value is
// cut to from the left. Each form's bits above 64 are read back through a
// select at or above bit 64.
TEST(BitsOfDeclaration, WideLiteralOfEachBaseCarriesItsHighBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] PL = 96'h0123_4567_89ab_cdef_0011_2233;\n"
      "  localparam int PLH = PL[95:64];\n"
      "  localparam logic [79:0] PB = 80'b"
      "1000000000000000000000000000000000000000"
      "0000000000000000000000000000000000000001;\n"
      "  localparam int PBH = PB[79:64];\n"
      "  localparam logic [71:0] PO = 72'O400000000000000000000001;\n"
      "  localparam int POH = PO[71:64];\n"
      "  localparam logic [79:0] PD = 80'd604462909807314587353089;\n"
      "  localparam int PDH = PD[79:64];\n"
      "  localparam logic [95:0] PX = 96'h0123_4567_89AB_CDEF_0011_22x3;\n"
      "  localparam int PXH = PX[95:64];\n"
      "  localparam logic [127:0] PW ="
      " 128'hFEDC_BA98_7654_3210_0123_4567_89AB_CDEF;\n"
      "  localparam int PWH = PW[127:96];\n"
      "  localparam int PWM = PW[95:64];\n"
      "  localparam logic [95:0] PZ = 96'h1;\n"
      "  localparam int PZH = PZ[95:64];\n"
      "  localparam int PZL = PZ[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "PLH"), 0x01234567);
  EXPECT_EQ(ParamValue(design, "PBH"), 0x8000);
  EXPECT_EQ(ParamValue(design, "POH"), 0x80);
  EXPECT_EQ(ParamValue(design, "PDH"), 0x8000);
  EXPECT_EQ(ParamValue(design, "PXH"), 0x00012345);
  EXPECT_EQ(ParamValue(design, "PWH"), 0xFEDCBA98);
  EXPECT_EQ(ParamValue(design, "PWM"), 0x76543210);
  EXPECT_EQ(ParamValue(design, "PZH"), 0);
  EXPECT_EQ(ParamValue(design, "PZL"), 1);
}

// §11.5.1 (printed page 296): a bit-select at or above bit 64 reads the bit
// the digits wrote there, a part-select running off the bottom of the value
// keeps its in-range bits at their places in the field with the bits below
// read as 0, and a bit-select below the range reads 0.
TEST(BitsOfDeclaration, BitSelectAboveSixtyFourAndBelowZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int B64 = P[64];\n"
      "  localparam int B67 = P[67];\n"
      "  localparam int B95 = P[95];\n"
      "  localparam int LOW = P[3:-4];\n"
      "  localparam int NEG = P[-1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "B64"), 1);
  EXPECT_EQ(ParamValue(design, "B67"), 0);
  EXPECT_EQ(ParamValue(design, "B95"), 0);
  EXPECT_EQ(ParamValue(design, "LOW"), 0x30);
  EXPECT_EQ(ParamValue(design, "NEG"), 0);
}

// §11.4.8 combines two 96-bit operands bit by bit across all 96, and §11.4.10
// shifts across them, the arithmetic right shift of a signed operand filling
// from its sign bit (PS, bit 95 set) and of one whose sign bit is clear (PP)
// or that is unsigned (P) with zeros. `P + 1` is arithmetic, which 994404a79
// carried across the words too; its low word here is the low word plus one,
// and test_elaborator_subclause_20_06_02b.cpp reads the carry above it.
TEST(BitsOfDeclaration, ShiftAndBitwiseOperatorsWorkAcrossTheWideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] M = 96'hF0F0_F0F0_F0F0_F0F0_F0F0_F0F0;\n"
      "  localparam logic signed [95:0] PS = "
      "96'sh8000_0000_0000_0000_0000_0001;\n"
      "  localparam logic signed [95:0] PP = "
      "96'sh0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] A = P & M;\n"
      "  localparam int AH = A[95:64];\n"
      "  localparam int AL = A[31:0];\n"
      "  localparam logic [95:0] O = P | M;\n"
      "  localparam int OH = O[95:64];\n"
      "  localparam logic [95:0] X = P ^ M;\n"
      "  localparam int XH = X[95:64];\n"
      "  localparam logic [95:0] N1 = P ~^ M;\n"
      "  localparam int N1H = N1[95:64];\n"
      "  localparam logic [95:0] N2 = P ^~ M;\n"
      "  localparam int N2H = N2[95:64];\n"
      "  localparam logic [95:0] SL = P << 4;\n"
      "  localparam int SLH = SL[95:64];\n"
      "  localparam int SLL = SL[31:0];\n"
      "  localparam logic [95:0] SW = P <<< 64;\n"
      "  localparam int SWH = SW[95:64];\n"
      "  localparam int SWL = SW[31:0];\n"
      "  localparam logic [95:0] SR = P >> 4;\n"
      "  localparam int SRH = SR[95:64];\n"
      "  localparam int SRL = SR[31:0];\n"
      "  localparam logic [95:0] SA = P >>> 4;\n"
      "  localparam int SAH = SA[95:64];\n"
      "  localparam logic signed [95:0] SS = PS >>> 4;\n"
      "  localparam int SSH = SS[95:64];\n"
      "  localparam logic signed [95:0] SQ = PP >>> 4;\n"
      "  localparam int SQH = SQ[95:64];\n"
      "  localparam logic signed [95:0] SM = PS & M;\n"
      "  localparam int SMH = SM[95:64];\n"
      "  localparam logic [95:0] I = P + 1;\n"
      "  localparam int IL = I[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "AH"), 0x00204060);
  EXPECT_EQ(ParamValue(design, "AL"), 0x00102030);
  EXPECT_EQ(ParamValue(design, "OH"), 0xF1F3F5F7);
  EXPECT_EQ(ParamValue(design, "XH"), 0xF1D3B597);
  EXPECT_EQ(ParamValue(design, "N1H"), 0x0E2C4A68);
  EXPECT_EQ(ParamValue(design, "N2H"), 0x0E2C4A68);
  EXPECT_EQ(ParamValue(design, "SLH"), 0x12345678);
  EXPECT_EQ(ParamValue(design, "SLL"), 0x01122330);
  EXPECT_EQ(ParamValue(design, "SWH"), 0x00112233);
  EXPECT_EQ(ParamValue(design, "SWL"), 0);
  EXPECT_EQ(ParamValue(design, "SRH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SRL"), 0xF0011223);
  EXPECT_EQ(ParamValue(design, "SAH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SSH"), 0xF8000000);
  EXPECT_EQ(ParamValue(design, "SQH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SMH"), 0x80000000);
  EXPECT_EQ(ParamValue(design, "IL"), 0x00112234);
}

// §23.10.2 with §6.20.2: an instance's parameter value assignment written as
// a literal names nothing and reads the same in every scope, so the bits
// above 64 of a 96-bit override are read where the instantiated module
// selects them; one written as the parent's parameter stands in the parent,
// whose names mean nothing in the child, so its words above bit 63 are
// recorded on the child's parameter as the value is resolved, against the
// parent's registration, and the child reads the same 0x01234567 through
// it. 64b2dfbe0 refolded a literal override alone and read 0 above bit 64
// through the second instance.
TEST(BitsOfDeclaration, LiteralOverrideReadsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(96'h0123_4567_89AB_CDEF_0011_2233)) u1();\n"
      "  c #(.P(PP)) u2();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 2u);
  auto value = [](const RtlirModule* c, std::string_view name) {
    for (const auto& p : c->params)
      if (p.name == name) return p.resolved_value;
    return int64_t{-1};
  };
  EXPECT_EQ(value(children[0].resolved, "H"), 0x01234567);
  EXPECT_EQ(value(children[0].resolved, "L"), 0x00112233);
  EXPECT_EQ(value(children[1].resolved, "H"), 0x01234567);
  EXPECT_EQ(value(children[1].resolved, "L"), 0x00112233);
}

// §20.6.2 (printed page 629) with §6.24.3: an unpacked array holds its
// element's bits per element, so `logic [7:0] arr[4]` is 32 bits, and a net
// is sized as a variable is -- `wire [3:0] v` four bits and `wire [7:0] w[3]`
// twenty-four. An array whose extent the declaration does not fix, a dynamic
// array, is left to the run.
TEST(BitsOfDeclaration, NetAndUnpackedArrayAnswerTheirBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [7:0] grid[2][3];\n"
      "  wire [7:0] w[3];\n"
      "  wire [3:0] v;\n"
      "  logic [7:0] dyn[];\n"
      "  localparam int BA = $bits(arr);\n"
      "  localparam int BG = $bits(grid);\n"
      "  localparam int BW = $bits(w);\n"
      "  localparam int BV = $bits(v);\n"
      "  localparam int BD = $bits(dyn);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "BA"), 32);
  EXPECT_EQ(ParamValue(design, "BG"), 48);
  EXPECT_EQ(ParamValue(design, "BW"), 24);
  EXPECT_EQ(ParamValue(design, "BV"), 4);
  EXPECT_TRUE(ParamUnresolved(design, "BD"));
  const auto* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->num_unpacked_dims, 1u);
  EXPECT_EQ(w->unpacked_dim_sizes, std::vector<uint32_t>{3});
  const auto* v = FindNet(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->num_unpacked_dims, 0u);
}

// §20.6.2 (printed page 629) with §6.18 (printed 118): a typedef name is
// sized by the type it stands for -- the clause's own `$bits(MyType)` of a
// structure typedef is 9 -- through the table a TypedefRegistryGuard installs
// over the scope being elaborated, so `localparam int BT = $bits(my_t)`
// reads 12 for `typedef logic [11:0] my_t`, the packed structure of a 4-bit
// and an 8-bit member reads 12, and a name standing for another name reads
// what that name does. d6a7eab50 left every typedef name to the run, the
// fold having reached no table, and pinned it here as
// TypedefNameIsLeftToTheRun; the queue typedef that stays refused is in
// test_elaborator_subclause_20_06_02b.cpp.
TEST(BitsOfDeclaration, TypedefNameAnswersItsTypeWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [11:0] my_t;\n"
      "  localparam int BT = $bits(my_t);\n"
      "  typedef struct packed { logic [3:0] a; logic [7:0] b; } s_t;\n"
      "  localparam int BS = $bits(s_t);\n"
      "  typedef s_t alias_t;\n"
      "  localparam int BA = $bits(alias_t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BT"), 12);
  EXPECT_EQ(ParamValue(design, "BS"), 12);
  EXPECT_EQ(ParamValue(design, "BA"), 12);
}

}  // namespace
