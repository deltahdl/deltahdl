// §6.16.1: Len()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.1: len() -- returns the length of the string
// =============================================================================
TEST(StringMethods, LenEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, LenBasic) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
}

}  // namespace
