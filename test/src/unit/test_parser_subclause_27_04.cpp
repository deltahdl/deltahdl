#include "fixture_parser.h"

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
  // A.4.2 ends loop_generate_construct with a generate_block, which is either a
  // single generate_item or a begin-end block, and gen_body_has_begin_end says
  // which was written here as it does for a conditional generate construct.
  // §27.5, printed page 825, rules that direct nesting "does not apply in any
  // way to loop generate constructs", so the field is recorded in this position
  // without that rule bearing on it: a loop generate block is a scope whether
  // or not begin and end were written.
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

}  // namespace
