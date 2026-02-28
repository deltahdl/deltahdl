// §27.3: Generate construct syntax

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfGenvarIdentifiersMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "j");
  EXPECT_EQ(r.cu->modules[0]->items[2]->name, "k");
}

TEST(ParserAnnexA, A4GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.4.2 -- Generated instantiation
//
// generate_region ::= generate { generate_item } endgenerate
//
// loop_generate_construct ::=
//   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
//     generate_block
//
// genvar_initialization ::= [ genvar ] genvar_identifier = constant_expression
//
// genvar_iteration ::=
//   genvar_identifier assignment_operator genvar_expression
//   | inc_or_dec_operator genvar_identifier
//   | genvar_identifier inc_or_dec_operator
//
// conditional_generate_construct ::=
//   if_generate_construct | case_generate_construct
//
// if_generate_construct ::=
//   if ( constant_expression ) generate_block [ else generate_block ]
//
// case_generate_construct ::=
//   case ( constant_expression ) case_generate_item { case_generate_item }
//     endcase
//
// case_generate_item ::=
//   constant_expression { , constant_expression } : generate_block
//   | default [ : ] generate_block
//
// generate_block ::=
//   generate_item
//   | [ generate_block_identifier : ] begin [ : generate_block_identifier ]
//       { generate_item } end [ : generate_block_identifier ]
//
// generate_item ::=
//   module_or_generate_item
//   | interface_or_generate_item
//   | checker_or_generate_item
// =============================================================================
// --- generate_region: basic ---
TEST(ParserAnnexA042, GenerateRegionBasic) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

// --- generate_region: empty ---
TEST(ParserAnnexA042, GenerateRegionEmpty) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// --- generate_region: multiple generate_items ---
TEST(ParserAnnexA042, GenerateRegionMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire a;\n"
      "    wire b;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// --- generate_block: begin/end with label ---
TEST(ParserAnnexA042, GenerateBlockLabeled) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    assign out[i] = in[i];\n"
      "  end : gen_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- generate_block: begin/end with multiple items ---
TEST(ParserAnnexA042, GenerateBlockMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  if (W > 0) begin\n"
      "    wire a;\n"
      "    assign a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_GE(gen->gen_body.size(), 2u);
}

bool HasItemOfKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- generate_region with mixed constructs ---
TEST(ParserAnnexA042, GenerateRegionMixedConstructs) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 2; i++) begin\n"
      "      wire w;\n"
      "    end\n"
      "    if (W > 0)\n"
      "      wire a;\n"
      "    case (SEL)\n"
      "      0: wire x;\n"
      "      default: wire y;\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateCase));
}

}  // namespace
