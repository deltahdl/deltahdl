#include <set>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventSimulationElaboration, ContinuousAssignIsRecognizedAsAProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->assigns.size(), 1u);
  ASSERT_EQ(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
  EXPECT_TRUE(mod->processes.empty());
}

TEST(EventSimulationElaboration, EveryProcessKindCarriesAnEvaluableBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d, e, en;\n"
      "  initial         a = 1'b0;\n"
      "  always_comb     b = a;\n"
      "  always_latch    if (en) c = a;\n"
      "  always_ff @(posedge a) d <= b;\n"
      "  final           e = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 5u);
  for (const auto& p : mod->processes) {
    EXPECT_NE(p.body, nullptr);
  }
}

TEST(EventSimulationElaboration, EnumeratedProceduralProcessKindsAreDistinct) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, en, a, b, c, d, e;\n"
      "  initial         a = 1'b0;\n"
      "  always @(a)     b = a;\n"
      "  always_comb     c = a;\n"
      "  always_latch    if (en) d = a;\n"
      "  always_ff @(posedge clk) e <= a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 5u);
  std::set<RtlirProcessKind> kinds;
  for (const auto& p : mod->processes) {
    kinds.insert(p.kind);
  }
  EXPECT_EQ(kinds.size(), 5u);
}

TEST(EventSimulationElaboration, ModuleWithoutProcessesHasEmptyProcessList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->processes.empty());
  EXPECT_TRUE(mod->assigns.empty());
}

TEST(EventSimulationElaboration, MultipleInitialBlocksProduceSeparateProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a = 1'b0;\n"
      "  initial b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_EQ(mod->processes[1].kind, RtlirProcessKind::kInitial);
}

}
