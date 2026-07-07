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

// §20.8 carry (usable in constant expressions, 11.2.1): the argument of $clog2
// may itself be a constant form other than a literal. Here a localparam value
// feeds the call, and the enclosing localparam folds to the ceiling-log2
// result during elaboration rather than merely parsing. DEPTH is 300, which
// sits between 2**8 and 2**9, so the address width resolves to 9.
TEST(ConstExprElab, Clog2OfParameterArgumentFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int DEPTH = 300;\n"
      "  localparam int AW = $clog2(DEPTH);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "AW") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 9);
    }
  }
  EXPECT_TRUE(found);
}

// §20.8 carry (constant-expression usage, 11.2.1): the constant-form argument
// may be a module parameter, which reaches constant evaluation through a
// different declaration path than a localparam. A parameter feeding $clog2 to
// size an address-width localparam folds during elaboration; DEPTH is 300, so
// the width resolves to 9.
TEST(ConstExprElab, Clog2OfPortParameterArgumentFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int DEPTH = 300);\n"
      "  localparam int AW = $clog2(DEPTH);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "AW") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 9);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
