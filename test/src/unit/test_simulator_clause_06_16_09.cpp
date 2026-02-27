// §6.16.9: Atoi(), atohex(), atooct(), atobin()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.9: atoi() / atohex() / atooct() / atobin()
// =============================================================================
TEST(StringMethods, Atoi) {
  StringFixture f;
  f.CreateStringVar("s", "42");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(StringMethods, Atohex) {
  StringFixture f;
  f.CreateStringVar("s", "1f");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x1fu);
}

TEST(StringMethods, Atooct) {
  StringFixture f;
  f.CreateStringVar("s", "77");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 077u);
}

TEST(StringMethods, Atobin) {
  StringFixture f;
  f.CreateStringVar("s", "1010");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1010u);
}

}  // namespace
