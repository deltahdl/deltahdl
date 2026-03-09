#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EnumMethods, NumSingleMember) {
  EnumFixture f;
  f.RegisterEnum("flag", "flag_t", {{"ONLY", 42}});
  auto* call = f.MakeEnumMethodCall("flag", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}
