#include <cstdint>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LexicalConventionElaboration, DefaultValueBitOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* full_case *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "full_case");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 1);
}

TEST(LexicalConventionElaboration, AttrValueFromLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "depth");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 8);
}

TEST(LexicalConventionElaboration, AttrValueFromConstExpr) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 3 + 5 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 8);
}

TEST(LexicalConventionElaboration, AttrValueZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state = 0 *) logic [3:0] reg2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 0);
}

TEST(LexicalConventionElaboration, AttrValueString) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* tool_purpose = \"synthesis\" *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "tool_purpose");
  EXPECT_EQ(mod->variables[0].attrs[0].string_value, "synthesis");
}

TEST(LexicalConventionElaboration, DuplicateAttrLastWins) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& attrs = design->top_modules[0]->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(a.resolved_value.value_or(INT64_MIN), 8);
    }
  }
  EXPECT_EQ(depth_count, 1);
}

TEST(LexicalConventionElaboration, DuplicateAttrWarning) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(LexicalConventionElaboration, DuplicateAttrAcrossInstances) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 2 *)\n"
      "  (* depth = 16 *)\n"
      "  logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& attrs = design->top_modules[0]->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(a.resolved_value.value_or(INT64_MIN), 16);
    }
  }
  EXPECT_EQ(depth_count, 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(LexicalConventionElaboration, AttrOnVarDecl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state *) logic [7:0] state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "fsm_state");
}

TEST(LexicalConventionElaboration, AttrOnNetDecl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* mark *) wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  ASSERT_FALSE(mod->nets[0].attrs.empty());
  EXPECT_EQ(mod->nets[0].attrs[0].name, "mark");
}

TEST(LexicalConventionElaboration, AttrOnContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *) assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_FALSE(mod->assigns[0].attrs.empty());
  EXPECT_EQ(mod->assigns[0].attrs[0].name, "synthesis_on");
}

TEST(LexicalConventionElaboration, AttrOnModuleInst) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub(input a);\n"
      "endmodule\n"
      "module m;\n"
      "  logic x;\n"
      "  (* optimize_power = 0 *) sub u1(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->children.empty());
  ASSERT_FALSE(mod->children[0].attrs.empty());
  EXPECT_EQ(mod->children[0].attrs[0].name, "optimize_power");
}

TEST(LexicalConventionElaboration, AttrOnModuleDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* optimize_power *)\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->attrs.empty());
  EXPECT_EQ(mod->attrs[0].name, "optimize_power");
}

TEST(LexicalConventionElaboration, AttrOnProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  (* synthesis = \"on\" *)\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  ASSERT_FALSE(mod->processes[0].attrs.empty());
  EXPECT_EQ(mod->processes[0].attrs[0].name, "synthesis");
}

TEST(LexicalConventionElaboration, MultipleDistinctAttrs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state, optimize = 1 *) logic [7:0] state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables[0].attrs.size(), 2u);
  EXPECT_EQ(mod->variables[0].attrs[0].name, "fsm_state");
  EXPECT_EQ(mod->variables[0].attrs[1].name, "optimize");
}

TEST(LexicalConventionElaboration, DuplicateLastNoValueDefaultsToOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 99, depth *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& attrs = design->top_modules[0]->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(a.resolved_value.value_or(INT64_MIN), 1);
    }
  }
  EXPECT_EQ(depth_count, 1);
}

TEST(LexicalConventionElaboration, NoErrorsWithAttributePresent) {
  ElabFixture f;
  ElaborateSrc(
      "(* optimize_power *)\n"
      "module m;\n"
      "  (* fsm_state *) logic [7:0] state;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *) assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionElaboration, ModuleWithAttributeElaborates) {
  EXPECT_TRUE(
      ElabOk("(* synthesis *) module t;\n"
             "  logic a;\n"
             "endmodule\n"));
}

}  // namespace
