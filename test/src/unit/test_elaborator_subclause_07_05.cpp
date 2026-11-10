#include <gtest/gtest.h>

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

TEST(DynamicArrayValidation, RealElementDynamicElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  real d[];\n"
             "endmodule\n"));
}

TEST(DynamicArrayValidation, StringElementDynamicElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string d[];\n"
             "endmodule\n"));
}

TEST(DynamicArrayValidation,
     DISABLED_NewOnADynamicArrayOfEnumsOrChandlesIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B, C} e_t;\n"
      "  e_t ed [] = new[2]; chandle cd [] = new[2]; e_t ee []; chandle ch "
      "[];\n"
      "  initial begin ee = new[3](ed); ee = new[4]; ch = new[2]; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
