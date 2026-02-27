// §10.3.3: Continuous assignment delays

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

}  // namespace
