#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventOrOperatorElaboration, OrSeparatedSensitivityElaborates) {
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

TEST(EventOrOperatorElaboration, CommaSeparatedSensitivityElaborates) {
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

TEST(EventOrOperatorElaboration, MixedOrAndCommaElaborates) {
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

TEST(EventOrOperatorElaboration, EdgeEventsWithOrElaborates) {
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

TEST(EventOrOperatorElaboration, SensitivityListPreservedInRtlir) {
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

TEST(EventOrOperatorElaboration, CommaSensitivityCountPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d, e, y;\n"
      "  always @(a, b, c, d, e) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_EQ(procs[0].sensitivity.size(), 5u);
}

TEST(EventOrOperatorElaboration, MixedOrCommaCountPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d, e, y;\n"
      "  always @(a or b, c, d or e) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_EQ(procs[0].sensitivity.size(), 5u);
}

}  // namespace
