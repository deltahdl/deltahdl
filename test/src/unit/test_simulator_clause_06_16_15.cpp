// §6.16.15: Realtoa()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.15: realtoa(r) -- assign real string representation to variable
// =============================================================================
TEST(StringMethods, Realtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  // Encode 2.5 as real (double) bits in an integer literal.
  double d = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  std::string result = VecToString(var->value);
  EXPECT_FALSE(result.empty());
  // The string should represent 2.5 in some decimal form.
  EXPECT_NE(result.find("2.5"), std::string::npos);
}

}  // namespace
