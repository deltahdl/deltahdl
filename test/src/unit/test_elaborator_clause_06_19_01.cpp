#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, EnumMembersAsConstants) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TypedefEnumElaboration, TypedefEnumTypeReusedForMultipleVars) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {OFF, ON} switch_t;\n"
      "  switch_t a;\n"
      "  switch_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& v : mod->variables) {
    if (v.name == "a" || v.name == "b") {
      EXPECT_EQ(v.enum_type_name, "switch_t") << v.name;
      ++count;
    }
  }
  EXPECT_EQ(count, 2);
}

TEST(Elaboration, TypedefEnumVarHasCorrectWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [3:0] {A, B, C} nibble_t;\n"
      "  nibble_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 4u);
      EXPECT_EQ(v.enum_type_name, "nibble_t");
    }
  }
}

}  // namespace
