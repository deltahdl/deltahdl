

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEvalReal, IntLiteralPromotesToReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("42", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 42.0);
}

}  // namespace
