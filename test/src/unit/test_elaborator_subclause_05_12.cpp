#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(LexicalConventionElaboration, SameNameDifferentElementsIndependent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 4 *) logic [7:0] a;\n"
      "  (* depth = 9 *) logic [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  const RtlirVariable* va = nullptr;
  const RtlirVariable* vb = nullptr;
  for (auto& v : mod->variables) {
    if (v.name == "a") va = &v;
    if (v.name == "b") vb = &v;
  }
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_FALSE(va->attrs.empty());
  ASSERT_FALSE(vb->attrs.empty());
  ASSERT_NE(va->attrs[0].resolved_value, std::nullopt);
  ASSERT_NE(vb->attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(va->attrs[0].resolved_value.value_or(INT64_MIN), 4);
  EXPECT_EQ(vb->attrs[0].resolved_value.value_or(INT64_MIN), 9);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
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

TEST(LexicalConventionElaboration, AttrValueFromLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam DEPTH = 12;\n"
      "  (* depth = DEPTH *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "depth");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 12);
}

TEST(LexicalConventionElaboration, AttrValueFromParameterOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter WIDTH = 4) ();\n"
      "  (* mem_width = WIDTH *) logic [7:0] mem;\n"
      "endmodule\n"
      "module top;\n"
      "  leaf #(.WIDTH(16)) u ();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const RtlirModule* top = nullptr;
  for (auto* m : design->top_modules) {
    if (m->name == "top") top = m;
  }
  ASSERT_NE(top, nullptr);
  ASSERT_FALSE(top->children.empty());
  const RtlirModule* leaf = top->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  ASSERT_FALSE(leaf->variables.empty());
  ASSERT_FALSE(leaf->variables[0].attrs.empty());
  EXPECT_EQ(leaf->variables[0].attrs[0].name, "mem_width");
  ASSERT_NE(leaf->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(leaf->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 16);
}

TEST(LexicalConventionElaboration, AttrValueNamingAParameterFoldsOnEachItem) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub; endmodule\n"
      "module m #(parameter P = 6);\n"
      "  (* depth = P *) wire w;\n"
      "  (* depth = P + 1 *) sub u();\n"
      "  (* depth = P + 2 *) initial begin end\n"
      "  (* depth = P + 3 *) assign w = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const RtlirModule* mod = nullptr;
  for (const RtlirModule* top : design->top_modules) {
    if (top->name == "m") mod = top;
  }
  ASSERT_NE(mod, nullptr);
  const auto kValueOf = [](const std::vector<ResolvedAttribute>& attrs) {
    return attrs.empty() ? std::nullopt : attrs[0].resolved_value;
  };
  std::optional<int64_t> net;
  for (const RtlirNet& n : mod->nets) {
    if (n.name == "w") net = kValueOf(n.attrs);
  }
  EXPECT_EQ(net, std::optional<int64_t>{6});
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(kValueOf(mod->children[0].attrs), std::optional<int64_t>{7});
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(kValueOf(mod->processes[0].attrs), std::optional<int64_t>{8});
  ASSERT_EQ(mod->assigns.size(), 1u);
  EXPECT_EQ(kValueOf(mod->assigns[0].attrs), std::optional<int64_t>{9});
}

TEST(LexicalConventionElaboration, AttrValueThatIsNotConstantIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int P = 3;\n"
      "  logic sig;\n"
      "  (* weight = sig *) logic x;\n"
      "  (* weight = sig + P *) logic y;\n"
      "  (* weight = P + 1 *) logic z;\n"
      "  (* weight = \"fast\" *) logic w;\n"
      "  (* weight = 1.5 *) logic v;\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "value of attribute 'weight' is not a constant expression";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "5.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "5.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(LexicalConventionElaboration, NodeAttrValueThatIsNotConstantIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic sig, x;\n"
      "  (* w = sig *) function void f(); endfunction\n"
      "  initial begin\n"
      "    (* w = sig *) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "value of attribute 'w' is not a constant expression";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 3, "5.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "5.12"));
}

TEST(LexicalConventionElaboration, ModuleAttrValueNamesUnitParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "localparam int U = 5;\n"
      "(* level = U + 1 *) module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(design->top_modules.size(), 1u);
  const auto& attrs = design->top_modules[0]->attrs;
  ASSERT_EQ(attrs.size(), 1u);
  EXPECT_EQ(attrs[0].resolved_value, std::optional<int64_t>{6});
}

TEST(LexicalConventionElaboration, ClassMemberAttrValueNamesClassParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C #(parameter int N = 2, type T = int,\n"
      "            parameter real R = 1.5);\n"
      "    localparam int K = 3;\n"
      "    int s;\n"
      "    (* w = N *) int a;\n"
      "    (* w = K + N *) int b;\n"
      "    (* w = s *) int c;\n"
      "    function void f(); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of attribute 'w' is not a constant "
                            "expression",
                            8, "5.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

std::vector<std::optional<int64_t>> NodeAttrValues(const RtlirModule& mod,
                                                   std::string_view name) {
  std::vector<std::optional<int64_t>> values;
  for (const auto& [node, attrs] : mod.node_attrs) {
    for (const ResolvedAttribute& attr : attrs) {
      if (attr.name == name) values.push_back(attr.resolved_value);
    }
  }
  std::sort(values.begin(), values.end());
  return values;
}

TEST(LexicalConventionElaboration, AttrValueNamesSubroutineAndBlockLocalParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int K = 9;\n"
      "  logic x;\n"
      "  function automatic int f();\n"
      "    localparam int L = 2;\n"
      "    (* weight = L *) return L;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      localparam int K = 3;\n"
      "      (* weight = K *) x = 1;\n"
      "    end\n"
      "    (* weight = K *) x = 0;\n"
      "    (* weight = L *) x = 1;\n"
      "    fork\n"
      "      localparam int J = 4;\n"
      "      (* weight = J *) x = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of attribute 'weight' is not a constant "
                            "expression",
                            14, "5.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
  ASSERT_EQ(design->top_modules.size(), 1u);
  const std::vector<std::optional<int64_t>> kExpected = {std::nullopt, 2, 3, 4,
                                                         9};
  EXPECT_EQ(NodeAttrValues(*design->top_modules[0], "weight"), kExpected);
}

TEST(LexicalConventionElaboration, AttrValueNamesUnfoldedClassParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 7;\n"
      "  class C #(parameter real R = 1.5, int P);\n"
      "    localparam real Q = 2.5;\n"
      "    (* scale = R *) int a;\n"
      "    (* width = P *) int b;\n"
      "    (* ratio = Q *) int c;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(design->top_modules.size(), 1u);
  const std::vector<std::optional<int64_t>> kNothing = {std::nullopt};
  EXPECT_EQ(NodeAttrValues(*design->top_modules[0], "width"), kNothing);
}

TEST(LexicalConventionElaboration, AssertionAttrReportsAreMadeOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, sig;\n"
      "  (* weight = sig *) assert property (@(posedge clk) a);\n"
      "  (* w = 1, w = 2 *) cover property (@(posedge clk) a);\n"
      "  (* weight = sig *) assert #0 (a);\n"
      "endmodule\n",
      f);
  const auto kCount = [&f](std::string_view message) {
    const auto& diags = f.diag.Diagnostics();
    return std::count_if(diags.begin(), diags.end(), [message](const auto& d) {
      return d.message == message;
    });
  };
  EXPECT_EQ(kCount("value of attribute 'weight' is not a constant expression"),
            2);
  EXPECT_EQ(kCount("duplicate attribute 'w'; last value used"), 1);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of attribute 'weight' is not a constant "
                            "expression",
                            3, "5.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of attribute 'weight' is not a constant "
                            "expression",
                            5, "5.12"));
}

}  // namespace
