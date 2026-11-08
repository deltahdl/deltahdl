#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(LoopGenerateParsing, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "i");
}

TEST(LoopGenerateParsing, GenvarMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j, k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->name, "i");
  EXPECT_EQ(mod->items[1]->name, "j");
  EXPECT_EQ(mod->items[2]->name, "k");
}

TEST(LoopGenerateParsing, ParameterizedModuleWithGenerate) {
  auto r = Parse(
      "module gray2bin #(parameter SIZE = 8) (\n"
      "  output [SIZE-1:0] bin,\n"
      "  input [SIZE-1:0] gray);\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < SIZE; i = i + 1) begin : bitnum\n"
      "      assign bin[i] = ^gray[SIZE-1:i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "gray2bin");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "SIZE");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(LoopGenerateParsing, GenvarDeclaredInsideGenerateRegion) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    genvar i;\n"
              "    for (i = 0; i < 2; i = i + 1) begin\n"
              "      wire w;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(LoopGenerateParsing, ForBodySingleItemRecordsNoBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  auto* loop = mod->items[1];
  ASSERT_EQ(loop->kind, ModuleItemKind::kGenerateFor);
  EXPECT_FALSE(loop->gen_body_has_begin_end);
}

TEST(LoopGenerateParsing, StepThatIsANonIncrementUnaryIsRejected) {
  auto r = Parse(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; ~i) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a loop generate's iteration is written",
                            4, "A.4.2"));
}

TEST(LoopGenerateParsing, InlineGenvarIsRecordedOnTheInitialization) {
  auto r = Parse(
      "module m;\n"
      "  genvar p;\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "  for (p = 0; p < 2; p++) begin : b end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3u);
  ASSERT_NE(mod->items[1]->gen_init, nullptr);
  EXPECT_EQ(mod->items[1]->gen_init->var_name, "i");
  ASSERT_NE(mod->items[2]->gen_init, nullptr);
  EXPECT_EQ(mod->items[2]->gen_init->var_name, "");
  EXPECT_EQ(mod->items[2]->gen_init->lhs->text, "p");
}

}  // namespace
