#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause09_02, AllSixProcedureTypesElaborate) {
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

TEST(ElabClause09_02, MultipleProcessesElaborate) {
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

TEST(ElabClause09_02, ProcessBodiesNotNull) {
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

}
TEST(StructuredProcedures, AllProcedureTypesCoexist) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb sum = a + b;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* sum = f.ctx.FindVariable("sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 30u);
}
