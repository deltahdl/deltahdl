#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TwoStateAndFourState, FourStateTypes) {
  EXPECT_TRUE(Is4stateType(DataTypeKind::kLogic));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kReg));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
  EXPECT_TRUE(Is4stateType(DataTypeKind::kTime));
}

TEST(TwoStateAndFourState, TwoStateTypes) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kByte));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kShortint));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
  EXPECT_FALSE(Is4stateType(DataTypeKind::kLongint));
}

TEST(TwoStateAndFourState, LogicAndRegBoth4State) {
  EXPECT_EQ(Is4stateType(DataTypeKind::kLogic),
            Is4stateType(DataTypeKind::kReg));
}

TEST(TwoStateAndFourState, TwoStateIntStoresFullWidth) {
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

TEST(TwoStateAndFourState, LogicAndRegElaborateIdentically) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  reg [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, mod->variables[1].width);
  EXPECT_EQ(mod->variables[0].is_4state, mod->variables[1].is_4state);
  EXPECT_EQ(mod->variables[0].is_signed, mod->variables[1].is_signed);
}

}  // namespace
