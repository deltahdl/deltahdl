#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Realtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");

  double d = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  std::string result = VecToString(var->value);
  EXPECT_FALSE(result.empty());

  EXPECT_NE(result.find("2.5"), std::string::npos);
}

TEST(StringMethods, RealtoaZero) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  double d = 0.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "0");
}

TEST(StringMethods, RealtoaOverwritesExisting) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "old");
  double d = 3.14;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  std::string result = VecToString(var->value);
  EXPECT_NE(result, "old");
  EXPECT_NE(result.find("3.14"), std::string::npos);
}

TEST(StringMethods, RealtoaIntegerValuedReal) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  double d = 42.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_NE(VecToString(var->value).find("42"), std::string::npos);
}

TEST(StringMethods, RealtoaNegativeValue) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  double d = -1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "-1.5");
}

// The text characterizes realtoa as the inverse of atoreal (§6.16.10): the real
// representation it stores must parse back to the original value. 2.5 is
// exactly representable at the default formatting precision, so the round trip
// is exact.
TEST(StringMethods, RealtoaIsInverseOfAtoreal) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  double d = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* store = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(store, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "2.5");

  auto* parse = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(parse, f.ctx, f.arena);
  double back = 0.0;
  uint64_t back_bits = result.ToUint64();
  std::memcpy(&back, &back_bits, sizeof(double));
  EXPECT_EQ(back, 2.5);
}

}  // namespace
