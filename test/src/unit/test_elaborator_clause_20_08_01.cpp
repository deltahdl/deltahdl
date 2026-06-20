#include "builders_ast.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Claim A: $clog2 folds to the ceiling of log base 2 during constant
// evaluation. Claim D: an argument of 0 (and the boundary value 1) folds to 0.
TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(0)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

// Claim B: the argument may be an arbitrary-sized vector value, not only a
// plain integer. A sized vector literal folds the same as the equivalent
// integer.
TEST(ConstEval, Clog2VectorArgument) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(16'd300)", f)), 9);
}

// Claim B edge case: an arbitrary-sized vector wider than the native machine
// integer folds correctly. 2**33 + 1 is just past a power of two, so the
// result rounds up to 34.
TEST(ConstEval, Clog2WideVectorArgument) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(40'd8589934593)", f)), 34);
}

// Claim C: the argument is treated as an unsigned value, so a negative input
// is folded over its (64-bit) unsigned bit pattern rather than collapsing to 0.
TEST(ConstEval, Clog2TreatsArgumentAsUnsigned) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(-1)", f)), 64);
}

TEST(SubroutineCallExprElaboration, SystemTfCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, PrimarySystemCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = $clog2(16);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
