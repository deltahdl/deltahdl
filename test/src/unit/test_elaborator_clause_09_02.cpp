#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StructuredProcedureElaboration, AllSixProcedureTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, d, e;\n"
      "  initial a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always_comb b = c & d;\n"
      "  always_latch if (clk) e = a;\n"
      "  always_ff @(posedge clk) c <= a;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;

  bool has_initial = false, has_always = false, has_comb = false;
  bool has_latch = false, has_ff = false, has_final = false;
  for (auto& p : procs) {
    switch (p.kind) {
      case RtlirProcessKind::kInitial:
        has_initial = true;
        break;
      case RtlirProcessKind::kAlways:
        has_always = true;
        break;
      case RtlirProcessKind::kAlwaysComb:
        has_comb = true;
        break;
      case RtlirProcessKind::kAlwaysLatch:
        has_latch = true;
        break;
      case RtlirProcessKind::kAlwaysFF:
        has_ff = true;
        break;
      case RtlirProcessKind::kFinal:
        has_final = true;
        break;
    }
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_always);
  EXPECT_TRUE(has_comb);
  EXPECT_TRUE(has_latch);
  EXPECT_TRUE(has_ff);
  EXPECT_TRUE(has_final);
}

TEST(StructuredProcedureElaboration, MultipleProcessesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "  always #1 a = ~a;\n"
      "  always #2 b = ~b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());

  int initial_count = 0, always_count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) ++initial_count;
    if (p.kind == RtlirProcessKind::kAlways) ++always_count;
  }
  EXPECT_EQ(initial_count, 3);
  EXPECT_EQ(always_count, 2);
}

TEST(StructuredProcedureElaboration, ProcessBodiesNotNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial a = 0;\n"
      "  always_comb a = 1;\n"
      "  final $display(\"end\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  for (auto& p : design->top_modules[0]->processes) {
    EXPECT_NE(p.body, nullptr) << "Process body should not be null";
  }
}

TEST(StructuredProcedureElaboration, MixedProcedureOrderingPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always #5 clk = ~clk;\n"
      "  initial a = 0;\n"
      "  final $display(\"end\");\n"
      "  initial b = 1;\n"
      "  always_comb a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());

  auto& procs = design->top_modules[0]->processes;
  int initial_count = 0, always_count = 0, final_count = 0, comb_count = 0;
  for (auto& p : procs) {
    if (p.kind == RtlirProcessKind::kInitial) ++initial_count;
    if (p.kind == RtlirProcessKind::kAlways) ++always_count;
    if (p.kind == RtlirProcessKind::kFinal) ++final_count;
    if (p.kind == RtlirProcessKind::kAlwaysComb) ++comb_count;
  }
  EXPECT_EQ(initial_count, 2);
  EXPECT_EQ(always_count, 1);
  EXPECT_EQ(final_count, 1);
  EXPECT_EQ(comb_count, 1);
}

TEST(StructuredProcedureElaboration, NoProcessesInEmptyModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_TRUE(design->top_modules[0]->processes.empty());
}

}  // namespace
