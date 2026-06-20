#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, BitsExpr) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
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
