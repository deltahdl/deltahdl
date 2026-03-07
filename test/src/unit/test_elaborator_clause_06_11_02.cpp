#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.11.2: 4-state types: logic, reg, integer, time.
TEST(TypeEval, FourStateTypes) {
  EXPECT_TRUE(Is4stateType(DataTypeKind::kLogic));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kReg));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kTime));
}

// §6.11.2: 2-state types: bit, byte, shortint, int, longint.
TEST(TypeEval, TwoStateTypes) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kByte));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kShortint));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kLongint));
}

// §6.11.2: logic and reg denote the same type.
TEST(TypeEval, LogicAndRegBoth4State) {
  EXPECT_EQ(Is4stateType(DataTypeKind::kLogic),
            Is4stateType(DataTypeKind::kReg));
}

TEST(SimCh10, VerifyWidthAndToUint64_32bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int val;\n"
      "  initial begin\n"
      "    val = 32'hDEADBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

}  // namespace
