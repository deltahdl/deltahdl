#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DynamicArrayValidation, UnsizedDimWithInitInferSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; int d [] = '{1,2,3}; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
  EXPECT_EQ(mod->variables[0].unpacked_size, 3u);
}

TEST(DynamicArrayValidation, UninitializedDefaultSizeZero) {
  ElabFixture f;
  auto* design = Elaborate("module m; int d []; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
  EXPECT_EQ(mod->variables[0].unpacked_size, 0u);
}

TEST(DynamicArrayValidation, PackedElementDynamicElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  bit [3:0] nibble[];\n"
             "endmodule\n"));
}

TEST(DynamicArrayValidation, LeftmostDimMustBeDynamicToBeDynamicArray) {
  ElabFixture f;
  auto* design = Elaborate("module m; integer mem[2][]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_FALSE(mod->variables[0].is_dynamic);
}

TEST(DynamicArrayValidation, LeftmostDynamicDimMakesArrayDynamic) {
  ElabFixture f;
  auto* design = Elaborate("module m; integer mem[][2]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
}

TEST(DynamicArrayValidation, DynamicArrayOfArraysElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int d[][];\n"
             "endmodule\n"));
}

}  // namespace
