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

// §9.4.2.1: a comma-separated sensitivity list shall be synonymous to the
// or-separated form. Elaborate one edge-qualified list spelled both ways and
// confirm the elaborator emits structurally identical RTLIR sensitivity
// (same length, same per-entry edge, same signal) for each spelling.
TEST(EventOrOperatorElaboration, CommaAndOrYieldIdenticalSensitivity) {
  ElabFixture fo;
  auto* or_design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, q;\n"
      "  always @(posedge clk or negedge rst) q = clk;\n"
      "endmodule\n",
      fo);
  ElabFixture fc;
  auto* comma_design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, q;\n"
      "  always @(posedge clk, negedge rst) q = clk;\n"
      "endmodule\n",
      fc);
  ASSERT_NE(or_design, nullptr);
  ASSERT_NE(comma_design, nullptr);
  EXPECT_FALSE(fo.has_errors);
  EXPECT_FALSE(fc.has_errors);
  ASSERT_FALSE(or_design->top_modules.empty());
  ASSERT_FALSE(comma_design->top_modules.empty());
  auto& or_procs = or_design->top_modules[0]->processes;
  auto& comma_procs = comma_design->top_modules[0]->processes;
  ASSERT_EQ(or_procs.size(), 1u);
  ASSERT_EQ(comma_procs.size(), 1u);

  auto& os = or_procs[0].sensitivity;
  auto& cs = comma_procs[0].sensitivity;
  ASSERT_EQ(os.size(), cs.size());
  ASSERT_EQ(os.size(), 2u);
  for (size_t i = 0; i < os.size(); ++i) {
    EXPECT_EQ(os[i].edge, cs[i].edge) << "entry " << i;
    ASSERT_NE(os[i].signal, nullptr) << "entry " << i;
    ASSERT_NE(cs[i].signal, nullptr) << "entry " << i;
    EXPECT_EQ(os[i].signal->text, cs[i].signal->text) << "entry " << i;
  }
}

}  // namespace
