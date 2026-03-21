#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EnumMethods, NumReturnsCount) {
  EnumFixture f;
  f.RegisterEnum("color", "color_t", {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  auto* call = f.MakeEnumMethodCall("color", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EnumMethods, NumSingleMember) {
  EnumFixture f;
  f.RegisterEnum("flag", "flag_t", {{"ONLY", 42}});
  auto* call = f.MakeEnumMethodCall("flag", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EnumMethods, NumLargeEnum) {
  EnumFixture f;
  std::vector<std::pair<std::string, uint64_t>> members;
  for (uint64_t i = 0; i < 256; ++i) {
    members.push_back({"E" + std::to_string(i), i});
  }
  f.RegisterEnum("big", "big_t", members);
  auto* call = f.MakeEnumMethodCall("big", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 256u);
}

TEST(EnumMethods, NumIndependentOfCurrentValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = f.MakeEnumMethodCall("color", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EnumMethods, NumReturnsIntWidth) {
  EnumFixture f;
  f.RegisterEnum("ab", "ab_t", {{"A", 0}, {"B", 1}});
  auto* call = f.MakeEnumMethodCall("ab", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(EnumMethods, NumEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "  int n;\n"
      "  initial n = c.num();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 3u);
}

TEST(EnumMethods, NumEndToEndSingleMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {SOLE} one_e;\n"
      "  one_e o;\n"
      "  int n;\n"
      "  initial n = o.num();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 1u);
}

}  // namespace
