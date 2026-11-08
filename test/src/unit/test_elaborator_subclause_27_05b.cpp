#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GenerateElaboration, DirectlyNestedIfBlockCollidesWithDeclaration) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  logic dup;\n"
      "  if (P) if (Q) begin : dup end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      3, "27.5"));
}

TEST(GenerateElaboration, DirectlyNestedCaseBlockCollidesWithDeclaration) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  wire w;\n"
      "  if (P) begin end else case (Q) 0: begin : w end\n"
      "    default: begin end endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'w' conflicts with another declaration in the same "
      "scope",
      3, "27.5"));
}

TEST(GenerateElaboration, DirectlyNestedBlockCollidesAcrossConstructs) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  if (P) begin : s end\n"
      "  if (Q) if (P) begin : s end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 's' has the same name as a "
                            "generate block in another generate construct",
                            3, "27.5"));
}

TEST(GenerateElaboration, DirectlyNestedBlocksMayShareTheOuterBlocksName) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  if (P) begin : u1 logic a; end\n"
      "  else case (Q)\n"
      "    0: begin : u1 logic b; end\n"
      "    default: begin : u1 logic c; end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(GenerateElaboration, BlockNameRulesHoldInsideAGenerateBlock) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  if (1) begin : outer\n"
      "    logic dup;\n"
      "    if (P) begin : dup end\n"
      "    if (P) begin : s end\n"
      "    case (P) 1: begin : s end\n"
      "             default: begin end endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      4, "27.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 's' has the same name as a "
                            "generate block in another generate construct",
                            6, "27.5"));
}

TEST(GenerateElaboration, BlockNameRulesHoldInUnselectedAndLoopBlocks) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  if (0) begin : never\n"
      "    wire d;\n"
      "    if (P) begin : d end\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : loop\n"
      "    logic e;\n"
      "    if (P) begin : e end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'd' conflicts with another declaration in the same "
      "scope",
      4, "27.5"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'e' conflicts with another declaration in the same "
      "scope",
      8, "27.5"));
}

TEST(GenerateElaboration, BlockNameRulesStayWithinOneScope) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  logic x;\n"
      "  if (1) begin : a\n"
      "    if (P) begin : x end\n"
      "  end\n"
      "  if (1) begin : b\n"
      "    if (P) begin : x end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(GenerateElaboration, SelfInstantiationEndsWhereTheConditionFails) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module r #(parameter N = 3) ();\n"
      "  if (N > 0) begin : sub\n"
      "    r #(.N(N - 1)) u ();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  r #(.N(2)) u ();\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  int depth = 0;
  const RtlirModule* mod = design->top_modules[0];
  while (!mod->children.empty()) {
    ASSERT_EQ(mod->children.size(), 1u);
    EXPECT_EQ(mod->children[0].module_name, "r");
    mod = mod->children[0].resolved;
    ASSERT_NE(mod, nullptr);
    ++depth;
  }
  EXPECT_EQ(depth, 3);
}

std::string BindInGenerateBlock(const char* cond) {
  return std::string(
             "module chk; endmodule\n"
             "module leaf; endmodule\n"
             "module top;\n"
             "  leaf u();\n"
             "  if (") +
         cond +
         ") begin : g\n"
         "    bind leaf chk c();\n"
         "  end\n"
         "endmodule\n";
}

int BoundInU(const RtlirDesign* design) {
  int count = 0;
  for (const auto& ch : design->top_modules[0]->children) {
    if (ch.inst_name != "u" || ch.resolved == nullptr) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == "c") ++count;
    }
  }
  return count;
}

TEST(GenerateElaboration, ABindInAnUnselectedBlockBindsNothing) {
  ElabFixture f;
  auto* design = ElaborateSrc(BindInGenerateBlock("0"), f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInU(design), 0);
}

TEST(GenerateElaboration, ABindInASelectedBlockBinds) {
  ElabFixture f;
  auto* design = ElaborateSrc(BindInGenerateBlock("1"), f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInU(design), 1);
}

}  // namespace
