#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
