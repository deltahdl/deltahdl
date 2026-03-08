// §11.8.2

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §11.2.1: ConstEvalReal — integer literal promotes to real.
TEST(ConstEvalReal, IntLiteralPromotesToReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("42", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 42.0);
}

}  // namespace
