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
  // §6.10: implicit declarations apply only to nets in specific contexts; an
  // undeclared name on a procedural assignment LHS is an error, so the
  // variables these processes drive must be declared explicitly.
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
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

TEST(StructuredProcedureElaboration,
     DynamicOverrideRejectedOnModuleLevelFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :initial int f(); return 0; endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StructuredProcedureElaboration, DynamicOverrideRejectedOnModuleLevelTask) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task :final t(); endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StructuredProcedureElaboration,
     DynamicOverrideExtendsRejectedOnModuleLevelTask) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task :extends t(); endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
