#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(GenerateRegion, DirectRegionNestingRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    generate\n"
      "    endgenerate\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, RegionNestedInGenerateIfBodyRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      generate\n"
      "      endgenerate\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, GenerateRegionAtModuleScopeAllowedOncePerSibling) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    wire a;\n"
              "  endgenerate\n"
              "  generate\n"
              "    wire b;\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(GenerateRegion, MissingEndgenerateRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, OptionalRegionKeywordsProduceSameItems) {
  auto with_region = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : blk\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  auto without_region = Parse(
      "module m;\n"
      "  if (1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(with_region.cu, nullptr);
  ASSERT_NE(without_region.cu, nullptr);
  EXPECT_FALSE(with_region.has_errors);
  EXPECT_FALSE(without_region.has_errors);
  ASSERT_EQ(with_region.cu->modules[0]->items.size(),
            without_region.cu->modules[0]->items.size());
  EXPECT_EQ(with_region.cu->modules[0]->items[0]->kind,
            without_region.cu->modules[0]->items[0]->kind);
}

TEST(GenerateRegion, EmptyRegionProducesNoItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// Syntax 27-1: case_generate_construct ::=
//   case ( constant_expression ) case_generate_item { case_generate_item }
//   endcase
// with case_generate_item carrying value labels or a default branch, each
// followed by a generate_block.
TEST(GenerateCaseConstruct, ValueAndDefaultItemsParse) {
  auto r = Parse(
      "module m;\n"
      "  parameter SEL = 0;\n"
      "  case (SEL)\n"
      "    0, 1: begin : lo\n"
      "      wire a;\n"
      "    end\n"
      "    default: begin : hi\n"
      "      wire b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ModuleItem* gen_case = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kGenerateCase) gen_case = it;
  }
  ASSERT_NE(gen_case, nullptr);
  // Two case_generate_items: the value item (labels 0, 1) and the default.
  ASSERT_EQ(gen_case->gen_case_items.size(), 2u);
  EXPECT_EQ(gen_case->gen_case_items[0].patterns.size(), 2u);
  EXPECT_FALSE(gen_case->gen_case_items[0].is_default);
  EXPECT_TRUE(gen_case->gen_case_items[1].is_default);
}

// Syntax 27-1: if_generate_construct ::=
//   if ( constant_expression ) generate_block [ else generate_block ]
// The optional else arm is recorded so both alternative blocks survive
// parsing.
TEST(GenerateIfConstruct, IfElseBlocksParse) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : t\n"
      "    wire a;\n"
      "  end else begin : f\n"
      "    wire b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  ASSERT_NE(mod->items[0]->gen_else, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_else->gen_body.empty());
}

// Syntax 27-1: loop_generate_construct ::=
//   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
//   generate_block
// genvar_initialization carries an optional inline genvar keyword; the three
// loop-control clauses are each captured.
TEST(GenerateLoopConstruct, ForWithInlineGenvarParsesAllClauses) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
      "    wire a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ModuleItem* loop = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kGenerateFor) loop = it;
  }
  ASSERT_NE(loop, nullptr);
  EXPECT_NE(loop->gen_init, nullptr);
  EXPECT_NE(loop->gen_cond, nullptr);
  EXPECT_NE(loop->gen_step, nullptr);
}

}  // namespace
