#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause1003, ContAssignDelayPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
}

TEST(ElabClause1003, ContAssignDelayRiseFall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(ElabClause1003, ContAssignDelayThreeValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_NE(mod->assigns[0].delay_decay, nullptr);
}

TEST(ElabClause100303, NettypeMultiDelay_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign #(5, 10) n = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElabClause100303, NettypeSingleDelay_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign #5 n = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause100303, NettypeThreeDelay_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign #(5, 10, 15) n = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElabClause100303, SingleDelayValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 10u);
}

TEST(ElabClause100303, RiseFallDelayValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 10u);
}

TEST(ElabClause100303, ThreeDelayValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 10u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 15u);
}

TEST(ElabClause100303, NoDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

}
