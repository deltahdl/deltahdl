#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConditionalEventIffElaboration, PosedgeIffElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en, q, d;\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConditionalEventIffElaboration, NegedgeIffElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en, q, d;\n"
      "  always @(negedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConditionalEventIffElaboration, NoEdgeIffElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a;\n"
      "  logic enable;\n"
      "  logic [31:0] y;\n"
      "  always @(a iff enable == 1) y <= a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConditionalEventIffElaboration, IffConditionPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en, q, d;\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  ASSERT_EQ(procs[0].sensitivity.size(), 1u);
  EXPECT_NE(procs[0].sensitivity[0].iff_condition, nullptr);
}

TEST(ConditionalEventIffElaboration, IffAbsentHasNullCondition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  ASSERT_EQ(procs[0].sensitivity.size(), 1u);
  EXPECT_EQ(procs[0].sensitivity[0].iff_condition, nullptr);
}

TEST(ConditionalEventIffElaboration, MixedIffPresencePreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, en, q;\n"
      "  always @(posedge clk iff en or negedge rst) q <= 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  ASSERT_EQ(procs[0].sensitivity.size(), 2u);
  EXPECT_NE(procs[0].sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(procs[0].sensitivity[1].iff_condition, nullptr);
}

TEST(ConditionalEventIffElaboration, BothEventsWithIffPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, en1, en2, q;\n"
      "  always @(posedge clk iff en1 or negedge rst iff en2) q <= 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  ASSERT_EQ(procs[0].sensitivity.size(), 2u);
  EXPECT_NE(procs[0].sensitivity[0].iff_condition, nullptr);
  EXPECT_NE(procs[0].sensitivity[1].iff_condition, nullptr);
}

TEST(ConditionalEventIffElaboration, AlwaysFFWithIffElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en;\n"
      "  logic [31:0] d, q;\n"
      "  always_ff @(posedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) {
      ASSERT_EQ(p.sensitivity.size(), 1u);
      EXPECT_NE(p.sensitivity[0].iff_condition, nullptr);
    }
  }
}

TEST(ConditionalEventIffElaboration, EdgeKeywordWithIffElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sig, guard, q;\n"
      "  always @(edge sig iff guard) q <= sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
