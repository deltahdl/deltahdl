// §6.19.5.5: Num()

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"

using namespace delta;

// =============================================================================
// Test fixture: sets up SimContext with an enum type and variable
// =============================================================================
namespace {

TEST(EnumMethods, NumSingleMember) {
  EnumFixture f;
  f.RegisterEnum("flag", "flag_t", {{"ONLY", 42}});
  auto* call = f.MakeEnumMethodCall("flag", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
