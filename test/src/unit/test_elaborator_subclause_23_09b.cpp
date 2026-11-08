#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

uint32_t WidthOfNetNamed(const RtlirModule* mod, std::string_view name) {
  const RtlirNet* found = nullptr;
  for (const auto& net : mod->nets) {
    if (net.name != name) continue;
    if (found != nullptr) return 0;
    found = &net;
  }
  return found == nullptr ? 0 : found->width;
}

TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInAModuleLevelExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "  endgenerate\n"
      "  wire [W-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "w"), 1U)
      << "block 'a' localparam W should not size a module-level net";
}

TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInASiblingBlockExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "    if (1) begin : c\n"
      "      wire [W-1:0] w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "c_w"), 1U)
      << "block 'a' localparam W should not size a sibling block's net";
}

TEST(GenerateBlockScope, ParameterOfAGenerateBlockStillFoldsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "block 'a' localparam W should size a net in block 'a'";
}

TEST(GenerateBlockScope, ParameterOfTheModuleStillFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter W = 4;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "the module's parameter W should size a net in block 'a'";
}

const RtlirParamDecl* OnlyChildParam(const RtlirModule* mod) {
  if (mod->children.size() != 1) return nullptr;
  const RtlirModule* child = mod->children[0].resolved;
  if (child == nullptr || child->params.size() != 1) return nullptr;
  return &child->params[0];
}

TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockIsNotReadByAModuleLevelDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "  endgenerate\n"
      "  defparam c.S = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_NE(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should not reach a module-level defparam";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam right-hand side must be a constant "
                            "expression built from numbers and parameters",
                            10, "23.10.1"));
}

TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockStillReadsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "      child c();\n"
      "      defparam c.S = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should reach a defparam in block 'a'";
}

TEST(GenerateBlockScope,
     StringLengthOfAGenerateBlockParameterDoesNotFoldInASiblingBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "    if (1) begin : b\n"
      "      localparam int N = P.len();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->resolved_value, 4)
      << "block 'a' localparam P should not be measured by len() in block 'b'";
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 7, "6.20.4"));
}

TEST(ScopeRulesElaboration, BareCallOfAnUndeclaredTaskIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    foo;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'foo'",
                            3, "23.9"));
}

TEST(ScopeRulesElaboration, BareCallOfAModuleTaskReportsNothing) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  task foo; endtask\n"
             "  initial foo;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, BareCallOfAUnitScopeTaskReportsNothing) {
  EXPECT_TRUE(
      ElabOk("task foo; endtask\n"
             "module m;\n"
             "  initial foo;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, BareCallOfAnImportedPackageTaskReportsNothing) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  task foo; endtask\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  initial foo;\n"
             "endmodule\n"));
}

}  // namespace
