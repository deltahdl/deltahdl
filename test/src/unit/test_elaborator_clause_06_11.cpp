// Non-LRM tests

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.11.1: Enum is integral.
TEST(TypeEval, EnumIsIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kEnum));
}

// §6.11.1: Non-integral types.
TEST(TypeEval, NonIntegralTypes) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kString));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

// §6.11.1: Built-in type widths per Table 6-8.
TEST(TypeEval, IntegerTypeWidths) {
  DataType dt;
  dt.kind = DataTypeKind::kByte;
  EXPECT_EQ(EvalTypeWidth(dt), 8u);
  dt.kind = DataTypeKind::kShortint;
  EXPECT_EQ(EvalTypeWidth(dt), 16u);
  dt.kind = DataTypeKind::kInt;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kLongint;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
  dt.kind = DataTypeKind::kInteger;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
  dt.kind = DataTypeKind::kTime;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(SimCh9, AlwaysCombResultWidth32) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  int result;\n"
      "  initial a = 100;\n"
      "  always_comb begin\n"
      "    result = a * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

}  // namespace
