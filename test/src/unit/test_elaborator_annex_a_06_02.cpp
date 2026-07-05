#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ProceduralBlockElaboration, InitialConstructElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial a = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

TEST(ProceduralBlockElaboration, AlwaysConstructElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlways);
}

TEST(ProceduralBlockElaboration, AlwaysCombElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb y = a & b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
}

TEST(ProceduralBlockElaboration, AlwaysLatchElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysLatch);
}

TEST(ProceduralBlockElaboration, AlwaysFFElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysFF);
}

TEST(ProceduralBlockElaboration, FinalConstructElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  final $display(\"end\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kFinal);
}

TEST(ProceduralBlockElaboration, AllFourAlwaysVariantsCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en, a, b, y1, y2, q1, q2;\n"
      "  always @(posedge clk) q1 = a;\n"
      "  always_comb y1 = a & b;\n"
      "  always_latch if (en) y2 = a;\n"
      "  always_ff @(posedge clk) q2 <= b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 4u);
  bool saw_always = false, saw_comb = false, saw_latch = false, saw_ff = false;
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlways) saw_always = true;
    if (p.kind == RtlirProcessKind::kAlwaysComb) saw_comb = true;
    if (p.kind == RtlirProcessKind::kAlwaysLatch) saw_latch = true;
    if (p.kind == RtlirProcessKind::kAlwaysFF) saw_ff = true;
  }
  EXPECT_TRUE(saw_always);
  EXPECT_TRUE(saw_comb);
  EXPECT_TRUE(saw_latch);
  EXPECT_TRUE(saw_ff);
}

TEST(ProceduralBlockElaboration, AlwaysCombInfersStarSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);

  EXPECT_TRUE(mod->processes[0].is_star_sensitivity ||
              !mod->processes[0].sensitivity.empty());
}

TEST(ProceduralBlockElaboration, BlockingAssignmentInInitial) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer a;\n"
      "  initial a = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralBlockElaboration, OperatorAssignmentInInitial) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer a;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    a += 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralBlockElaboration, ProceduralForceReleaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    force a = b;\n"
      "    release a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralBlockElaboration, ProceduralAssignDeassignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    assign a = b;\n"
      "    deassign a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralBlockElaboration, IncDecExpressionCrossLinkInInitial) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    i++;\n"
      "    ++i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
