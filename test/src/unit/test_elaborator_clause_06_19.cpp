#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, EnumSizedLiteralMismatch_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum logic [2:0] {\n"
      "    Global = 4'h2,\n"
      "    Local = 4'h3\n"
      "  } myenum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumXZin2State_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumDuplicateValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum {a=0, b=7, c, d=8} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumDefaultWidthInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum {A, B, C} x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 32u);
    }
  }
}

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

TEST(Elaboration, EnumExplicitBaseWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum logic [3:0] {A, B, C} x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumDuplicateName_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum {A, B, A} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumAutoIncrementOverflow_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [0:0] {A, B, C} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumAutoIncrementValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B=5, C} color_t;\n"
      "  color_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("color_t");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "A");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "B");
  EXPECT_EQ(it->second[1].value, 5);
  EXPECT_EQ(it->second[2].name, "C");
  EXPECT_EQ(it->second[2].value, 6);
}

}  // namespace
