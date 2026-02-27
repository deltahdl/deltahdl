// §6.16.10: Atoreal()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.10: atoreal() -- convert string to real
// =============================================================================
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

}  // namespace
