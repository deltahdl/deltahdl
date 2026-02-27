// §20.8.1: Integer math functions

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

// § system_tf_call — $clog2 as expression elaborates
TEST(ElabA82, SystemTfCallAsExprElaborates) {
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

// § primary — system call elaborates
TEST(ElabA84, PrimarySystemCallElaborates) {
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
