#include "fixture_parser.h"

using namespace delta;

namespace {

// Finds the first parameter-declaration item nested inside generate bodies.
const ModuleItem* FindParamInGenerate(const ModuleItem* item) {
  if (!item) return nullptr;
  for (const auto* child : item->gen_body) {
    if (child->kind == ModuleItemKind::kParamDecl) return child;
    if (const auto* found = FindParamInGenerate(child)) return found;
  }
  if (item->gen_else) {
    if (const auto* found = FindParamInGenerate(item->gen_else)) return found;
  }
  for (const auto& ci : item->gen_case_items) {
    for (const auto* child : ci.body) {
      if (child->kind == ModuleItemKind::kParamDecl) return child;
      if (const auto* found = FindParamInGenerate(child)) return found;
    }
  }
  return nullptr;
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    specify endspecify\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    specify endspecify\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, SpecifyBlockRejectedInGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin specify endspecify end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, SpecifyBlockAllowedAtModuleScope) {
  EXPECT_TRUE(ParseOk(
      "module m(input a, output b);\n"
      "  specify endspecify\n"
      "endmodule\n"));
}

TEST(GenerateBlockContent, SpecifyBlockAllowedInBareGenerateRegion) {
  // Items directly under `generate ... endgenerate` without an enclosing
  // for/if/case body are module items, not generate-block contents, so the
  // §27.2 restriction does not apply here.
  EXPECT_TRUE(ParseOk(
      "module m(input a, output b);\n"
      "  generate\n"
      "    specify endspecify\n"
      "  endgenerate\n"
      "endmodule\n"));
}

TEST(GenerateBlockContent, SpecparamRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    specparam t = 1.0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, SpecparamRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    specparam t = 1.0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, SpecparamRejectedInSingleItemGenerateBody) {
  // `generate_block ::= generate_item` — a single-item body without begin/end.
  auto r = Parse(
      "module m;\n"
      "  if (1) specparam t = 1.0;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, PortDeclarationRejectedInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    input a;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, PortDeclarationRejectedInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    output b;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateBlockContent, ParameterPromotedToLocalparamInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : blk\n"
      "    parameter int P = 7;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockContent, ParameterPromotedToLocalparamInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    parameter int Q = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[1];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockContent, ParameterPromotedToLocalparamInGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin parameter int R = 2; end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockContent, ParameterPromotedInNestedGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      parameter int S = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0]->items[0];
  const auto* p = FindParamInGenerate(outer);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockContent, ParameterPromotedInSingleItemGenerateBody) {
  auto r = Parse(
      "module m;\n"
      "  if (1) parameter int P = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockContent, ParameterAtModuleScopeNotPromoted) {
  // Outside any generate block, `parameter` remains a regular parameter and
  // is not promoted to a localparam by §27.2.
  auto r = Parse(
      "module m;\n"
      "  parameter int P = 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(item->is_localparam);
}

TEST(GenerateBlockContent, GenerateBlockAcceptsMultipleModuleItems) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  if (1) begin\n"
      "    wire w;\n"
      "    logic l;\n"
      "    assign w = l;\n"
      "    initial begin end\n"
      "  end\n"
      "endmodule\n"));
}

TEST(GenerateBlockContent, GenerateBlockAcceptsNestedGenerateConstruct) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      wire w;\n"
      "    end\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
