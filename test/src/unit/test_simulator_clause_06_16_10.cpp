#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Atoreal) {
  StringFixture f;
  f.CreateStringVar("s", "3.14");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 3.14, 0.001);
}

TEST(StringMethods, AtorealEmptyStringReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_EQ(d, 0.0);
}

TEST(StringMethods, AtorealNoDigitsReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_EQ(d, 0.0);
}

TEST(StringMethods, AtorealExponentNotation) {
  StringFixture f;
  f.CreateStringVar("s", "1.5e2");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 150.0, 0.001);
}

TEST(StringMethods, AtorealStopsAtNonConforming) {
  StringFixture f;
  f.CreateStringVar("s", "2.5xyz");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 2.5, 0.001);
}

TEST(StringMethods, AtorealIntegerString) {
  StringFixture f;
  f.CreateStringVar("s", "42");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 42.0, 0.001);
}

}  // namespace
