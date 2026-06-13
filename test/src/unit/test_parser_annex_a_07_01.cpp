#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(SpecifyBlockDeclParsing, PulsestyleAndShowcancelledTogether) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect out1;\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 2u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(spec->specify_items[1]->is_noshowcancelled);
}

// specify_block ::= specify { specify_item } endspecify
// Zero-repetition of { specify_item }: an empty specify block must parse.
TEST(SpecifyBlockDeclParsing, EmptySpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items.empty());
}

// pulsestyle_declaration ::= pulsestyle_onevent list_of_path_outputs ; | ...
// Complements the ondetect alternative covered above.
TEST(SpecifyBlockDeclParsing, PulsestyleOnevent) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(spec->specify_items[0]->is_ondetect);
}

// showcancelled_declaration ::= ... | noshowcancelled list_of_path_outputs ;
// Complements the showcancelled alternative covered above.
TEST(SpecifyBlockDeclParsing, NoshowcancelledDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
}

// specify_item ::= specparam_declaration | ...
// The specify_item dispatch routes a specparam declaration to a specparam item.
TEST(SpecifyBlockDeclParsing, SpecparamAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tHL = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

// specify_item ::= ... | path_declaration | ...
// The specify_item dispatch routes a path declaration to a path-decl item.
TEST(SpecifyBlockDeclParsing, PathDeclarationAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
}

// specify_item ::= ... | system_timing_check
// The specify_item dispatch routes a system timing check to a timing-check item.
TEST(SpecifyBlockDeclParsing, SystemTimingCheckAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge c, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kTimingCheck);
}

// pulsestyle_declaration ::= pulsestyle_onevent list_of_path_outputs ; | ...
// The trailing ';' is a required terminal of the production: dropping it is an
// error. The item is still produced, so the parser reached the ';' check.
TEST(SpecifyBlockDeclParsing, PulsestyleDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

// showcancelled_declaration ::= showcancelled list_of_path_outputs ; | ...
// The trailing ';' terminal is required; omitting it is an error.
TEST(SpecifyBlockDeclParsing, ShowcancelledDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
}

// specify_block ::= specify { specify_item } endspecify
// The closing endspecify keyword is a required terminal; a block left open
// (here at end of input) is an error.
TEST(SpecifyBlockDeclParsing, SpecifyBlockMissingEndspecifyRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}
