#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause09_04_02_01, OrSeparatedSensitivityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @(a or b) y = a & b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_02_01, CommaSeparatedSensitivityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, y;\n"
      "  always @(a, b, c) y = a | b | c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_02_01, MixedOrAndCommaElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, y;\n"
      "  always @(a or b, c) y = a ^ b ^ c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_02_01, EdgeEventsWithOrElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk_a, clk_b, q;\n"
      "  always @(posedge clk_a or posedge clk_b) q <= 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_02_01, SensitivityListPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, q;\n"
      "  always_ff @(posedge clk or negedge rst)\n"
      "    if (!rst) q <= 0;\n"
      "    else q <= 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) {
      EXPECT_EQ(p.sensitivity.size(), 2u);
    }
  }
}

}
