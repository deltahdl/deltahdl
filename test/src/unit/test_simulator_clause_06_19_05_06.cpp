#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

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

TEST(EnumMethods, NameForLastMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "BLUE");
}

TEST(EnumMethods, NameForSingleMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("flag", "flag_t", {{"ONLY", 42}});
  var->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto* call = f.MakeEnumMethodCall("flag", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(ExtractEnumName(result), "ONLY");
}

TEST(EnumMethods, NameForUnknownValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, NameReturnsCorrectStringWidth) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // "GREEN" is 5 characters, so width should be 5 * 8 = 40 bits.
  EXPECT_EQ(result.width, 40u);
}

TEST(EnumMethods, NameEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "  string s;\n"
      "  initial begin\n"
      "    c = GREEN;\n"
      "    s = c.name();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.ToUint64(), 0u);
}

}  // namespace
