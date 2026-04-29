#include <set>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §4.3 ¶2: "Examples of processes include... always_comb procedures...". The
// elaborator's AddProcess path constructs an RtlirProcess of kind kAlwaysComb
// for an always_comb procedure and infers its sensitivity from the body when
// none is written explicitly.
TEST(EventSimulationElaboration, AlwaysCombIsRecognizedAsAProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_NE(mod->processes[0].body, nullptr);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

// §4.3 ¶2: "Examples of processes include... always_latch procedures...". The
// elaborator constructs an RtlirProcess of kind kAlwaysLatch for an
// always_latch procedure and infers its sensitivity from the body.
TEST(EventSimulationElaboration, AlwaysLatchIsRecognizedAsAProcess) {
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
  EXPECT_NE(mod->processes[0].body, nullptr);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

// §4.3 ¶2: "Examples of processes include... continuous assignments...". The
// elaborator records each continuous assignment in the module's `assigns`
// list as a distinct process-like construct, separate from procedural
// `processes`. Both LHS and RHS are captured as evaluable expressions.
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

// §4.3 ¶2: "Processes are objects that can be evaluated". Every elaborated
// RtlirProcess carries a non-null body that the simulator later evaluates;
// a null body would prevent evaluation.
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

// §4.3 ¶2: the enumerated procedural process kinds (initial, always,
// always_comb, always_latch, always_ff) all elaborate into distinct
// RtlirProcessKind values. A module containing one of each exposes the full
// set so the simulator can later schedule each as its own process.
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

// §4.3 ¶2 edge case: a module with no procedural processes elaborates to an
// empty `processes` list. The "concurrently scheduled elements" of §4.3 ¶2
// only exist when the source declares them.
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

// §4.3 ¶2 multiplicity: two procedures of the same kind in the same module
// elaborate to two separate RtlirProcess entries — each is a "concurrently
// scheduled" process per §4.3 ¶2, not a merged single process.
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

}  // namespace
