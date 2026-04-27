#include "fixture_parser.h"

using namespace delta;

namespace {

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
