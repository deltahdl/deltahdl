// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §11.2.1: Unbased unsized literal is a constant expression.
TEST(ConstExpr, UnbasedUnsizedLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("'1", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

}  // namespace
