// §6.16.3: Getc()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.3: getc(i) -- return byte at index i
// =============================================================================
TEST(StringMethods, Getc) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('e'));
}

}  // namespace
