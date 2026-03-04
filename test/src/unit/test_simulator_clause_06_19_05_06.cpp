#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/eval.h"

using namespace delta;

static std::string ExtractEnumName(const Logic4Vec& result) {
  std::string name_str;
  uint64_t v = result.ToUint64();
  uint32_t nbytes = (result.width + 7) / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    auto ch = static_cast<char>((v >> ((i - 1) * 8)) & 0xFF);
    if (ch != 0) name_str += ch;
  }
  return name_str;
}

namespace {

TEST(EnumMethods, NameReturnsStringRep) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "GREEN");
}

TEST(EnumMethods, NameForFirstMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "RED");
}

}
