#include "fixture_elaborator.h"

namespace {

// --- module_common_item elaboration ---

TEST(ModuleItemsElaboration, ContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
}

TEST(ModuleItemsElaboration, InitialBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kInitial);
}

TEST(ModuleItemsElaboration, FinalBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  final begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kFinal);
}

TEST(ModuleItemsElaboration, AlwaysCombProcessKind) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  always_comb begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysComb);
}

TEST(ModuleItemsElaboration, AlwaysFFProcessKind) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  always_ff @(posedge clk) begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysFF);
}

TEST(ModuleItemsElaboration, AlwaysLatchProcessKind) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  always_latch begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysLatch);
}

TEST(ModuleItemsElaboration, AlwaysPlainProcessKind) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  always @(posedge clk) begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->processes.empty());
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlways);
}

TEST(ModuleItemsElaboration, ModuleInstantiationElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module m;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->children.empty());
  EXPECT_EQ(design->top_modules[0]->children[0].module_name, "child");
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "u1");
}

TEST(ModuleItemsElaboration, EmptyModuleElaborates) {
  ElabFixture f;
  auto* design = Elaborate("module m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(design->top_modules[0]->processes.empty());
  EXPECT_TRUE(design->top_modules[0]->assigns.empty());
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(ModuleItemsElaboration, MultipleItemKindsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1;\n"
      "  initial begin end\n"
      "  always_comb begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
  EXPECT_GE(design->top_modules[0]->processes.size(), 2u);
}

// --- elaboration_severity_system_task ---

TEST(ElaborationSeverityTaskElab, InfoDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, WarningDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $warning(\"potential issue\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, FatalValidFinishNumbers) {
  for (int fn = 0; fn <= 2; ++fn) {
    ElabFixture f;
    auto src = "module m; $fatal(" + std::to_string(fn) + "); endmodule\n";
    auto* design = Elaborate(src, f);
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors) << "finish_number " << fn << " should be valid";
  }
}

TEST(ElaborationSeverityTaskElab, FatalInvalidFinishNumber) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, FatalNoArgsIsValid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- parameter_override (defparam) elaboration ---

TEST(ParameterOverrideElab, DefparamOverridesChildParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child #(parameter int W = 8);\n"
      "endmodule\n"
      "module m;\n"
      "  child u1();\n"
      "  defparam u1.W = 32;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->children.empty());
}

// --- non_port_module_item: nested declarations ---

TEST(ModuleItemsElaboration, NestedModuleDoesNotAffectParent) {
  ElabFixture f;
  auto* design = Elaborate(
      "module inner; endmodule\n"
      "module m;\n"
      "  module inner_nested; endmodule\n"
      "  wire a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- generate constructs elaborate ---

TEST(ModuleItemsElaboration, ConditionalGenerateElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  if (1) begin : yes\n"
      "    wire a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, LoopGenerateElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleItemsElaboration, GenerateRegionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
