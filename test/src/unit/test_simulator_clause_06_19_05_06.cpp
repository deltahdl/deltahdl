// §6.19.5.6: Name()

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"

using namespace delta;

// =============================================================================
// Test fixture: sets up SimContext with an enum type and variable
// =============================================================================
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

// =============================================================================
// §6.19.5.6: name() — returns the string name of the current value
// =============================================================================
TEST(EnumMethods, NameReturnsStringRep) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);  // GREEN
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "GREEN");
}

TEST(EnumMethods, NameForFirstMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);  // RED
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "RED");
}

}  // namespace
