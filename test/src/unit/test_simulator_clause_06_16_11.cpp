#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Itoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(123)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "123");
}

TEST(StringMethods, ItoaZero) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(0)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "0");
}

TEST(StringMethods, ItoaOverwritesExisting) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "old");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(456)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "456");
}

// Storing into str fully replaces the prior contents rather than overwriting in
// place: a shorter decimal result leaves no residual trailing characters from a
// longer previous value.
TEST(StringMethods, ItoaReplacesLongerExisting) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "999999");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(7)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "7");
}

// The decimal text itoa stores is the inverse of the atoi conversion: scanning
// the produced string back with atoi recovers the original integer value.
TEST(StringMethods, ItoaIsInverseOfAtoi) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* store = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(2024)});
  EvalExpr(store, f.ctx, f.arena);
  auto* back = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(back, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2024u);
}

}  // namespace
