#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    specify endspecify\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 3, "27.2"));
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    specify endspecify\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 4, "27.2"));
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin specify endspecify end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 3, "27.2"));
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInNestedGenerate) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      specify endspecify\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 4, "27.2"));
}

TEST(GenerateBlockContent, SpecifyBlockAllowedAtModuleScope) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify endspecify\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInBareGenerateRegion) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  generate\n"
      "    specify endspecify\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block or region", 3,
      "A.4.2"));
}

TEST(GenerateBlockContent, SpecparamRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    specparam t = 1.0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            3, "27.2"));
}

TEST(GenerateBlockContent, SpecparamRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    specparam t = 1.0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            4, "27.2"));
}

TEST(GenerateBlockContent, SpecparamRejectedInSingleItemGenerateBody) {
  auto r = Parse(
      "module m;\n"
      "  if (1) specparam t = 1.0;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            2, "27.2"));
}

TEST(GenerateBlockContent, SpecparamAllowedAtModuleScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  specparam t = 1.0;\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    input a;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 3,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    output b;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 4,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedInGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin input a; end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 3,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedInNestedGenerate) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      inout c;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 4,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedWithRefDirection) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    ref r;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 3,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationAllowedAtModuleScope) {
  EXPECT_TRUE(
      ParseOk("module m(a, b);\n"
              "  input a;\n"
              "  output b;\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, GenerateBlockAcceptsMultipleModuleItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) begin\n"
              "    wire w;\n"
              "    logic l;\n"
              "    assign w = l;\n"
              "    initial begin end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, GenerateBlockAcceptsSingleModuleItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) wire w;\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, GenerateBlockAcceptsNestedGenerateConstruct) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) begin\n"
              "    if (1) begin\n"
              "      wire w;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateBlockContent, TypedPortDeclarationRejectedAsASingleItemBody) {
  auto r = Parse(
      "module m;\n"
      "  if (1) input logic [3:0] a;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 2,
      "27.2"));
}

TEST(GenerateBlockContent, EachForbiddenItemRejectedInABlockInsideARegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      input a;\n"
      "      specify endspecify\n"
      "      specparam t = 1.0;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 4,
      "27.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 5, "27.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            6, "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationRejectedInInterfaceAndProgramBlocks) {
  auto r = Parse(
      "interface i;\n"
      "  if (1) begin\n"
      "    input a;\n"
      "  end\n"
      "endinterface\n"
      "program p;\n"
      "  if (1) begin\n"
      "    output b;\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 3,
      "27.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "port declaration not allowed inside a generate block", 8,
      "27.2"));
}

TEST(GenerateBlockContent, PortDeclarationAllowedInInterfaceAndProgramBodies) {
  EXPECT_TRUE(
      ParseOk("interface i(a);\n"
              "  input a;\n"
              "endinterface\n"
              "program p(b);\n"
              "  output b;\n"
              "endprogram\n"));
}

TEST(GenerateBlockContent, SpecifyBlockRejectedAsASingleItemBody) {
  auto r = Parse(
      "module m;\n"
      "  if (1) specify endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block not allowed inside a generate block", 2, "27.2"));
}

TEST(GenerateBlockContent, SpecparamRejectedInCaseAndNestedGenerateBlocks) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin specparam t = 1.0; end\n"
      "    default: ;\n"
      "  endcase\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      specparam u = 2.0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            3, "27.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block",
                            8, "27.2"));
}

TEST(GenerateBlockContent, GenerateBlockParameterIsLocalInInterfaceAndProgram) {
  auto r = Parse(
      "interface i;\n"
      "  parameter int B = 1;\n"
      "  if (1) begin : g\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "endinterface\n"
      "program p;\n"
      "  parameter int B = 1;\n"
      "  if (1) begin : g\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  for (const auto& items :
       {r.cu->interfaces[0]->items, r.cu->programs[0]->items}) {
    ASSERT_EQ(items.size(), 2u);
    ASSERT_EQ(items[0]->kind, ModuleItemKind::kParamDecl);
    EXPECT_FALSE(items[0]->is_localparam);
    ASSERT_EQ(items[1]->kind, ModuleItemKind::kGenerateIf);
    ASSERT_EQ(items[1]->gen_body.size(), 1u);
    ASSERT_EQ(items[1]->gen_body[0]->kind, ModuleItemKind::kParamDecl);
    EXPECT_TRUE(items[1]->gen_body[0]->is_localparam);
  }
}

}  // namespace
