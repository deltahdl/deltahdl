#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(SpecifyBlockDeclParsing, SpecifyBlockEmpty) {
  auto r = Parse("module m; specify endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(spec->specify_items.size(), 0u);
}

TEST(SpecifyBlockDeclParsing, SpecifyBlockCoexistsWithModuleItems) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  assign a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

TEST(SpecifyBlockDeclParsing, MultipleSpecifyBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  specify\n"
      "    (c => d) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  int spec_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) ++spec_count;
  }
  EXPECT_EQ(spec_count, 2);
}

TEST(SpecifyBlockDeclParsing, SpecifyItemAllFiveKinds) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

TEST(SpecifyBlockDeclParsing, TimingCheckMixedWithPaths) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = 5;\n"
      "  $setup(data, posedge clk, 10);\n"
      "  (c *> d) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
}

TEST(SpecifyBlockDeclParsing, SpecifyBlockSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
}

TEST(SpecifyBlockDeclParsing, ErrorMissingEndspecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "endmodule\n");
  // The specify block runs to the `endmodule` on line 4, which stands where
  // the `endspecify` that closes it belongs.
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endspecify', got 'endmodule'",
                            4, "30.3"));
}

TEST(SpecifyBlockDeclParsing, ErrorSpecifyOutsideModule) {
  auto r = Parse(
      "specify\n"
      "  (a => b) = 5;\n"
      "endspecify\n");
  // §3.12.1 owns the set of top-level descriptions, and that is the rule the
  // parser reports for a specify block at file scope; §30.3 has no report here.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"));
}

TEST(SpecifyBlockDeclParsing, ErrorSpecifyInsidePackage) {
  auto r = Parse(
      "package p;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
}

TEST(SpecifyBlockDeclParsing, ErrorUnknownSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    initial x = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in specify block", 3, "30.3"));
}

// A specify_item admits system_timing_check as its only system-call form, so a
// general system task (here $display) is not a valid specify_item and the
// parser must reject it.
TEST(SpecifyBlockDeclParsing, ErrorNonTimingCheckSystemTask) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $display(\"hi\");\n"
      "  endspecify\n"
      "endmodule\n");
  // §31.2 owns the system timing checks a specify block admits, and the parser
  // files the rejection of any other system task under it, not under §30.3.
  EXPECT_TRUE(ReportedError(
      r.diags, "system task cannot appear in specify block", 3, "31.2"));
}

TEST(SpecifyBlockDeclParsing, ErrorStrayEndspecify) {
  auto r = Parse(
      "module m;\n"
      "  endspecify\n"
      "endmodule\n");
  // §23.2.4 owns the module item list, and a stray endspecify is reported as a
  // module body item there rather than under §30.3.
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(SpecifyBlock, MalformedPathDeclarationNames30_3) {
  // §30.3, Syntax 30-1: specify_item admits a path_declaration, and every
  // path_declaration form opens with the '(' of a path description. A source
  // that starts one with a bare terminal name matches no specify_item, and the
  // report names §30.3 so a case can tell this rejection from the timing-check
  // and edge-descriptor rules a specify block breaks with the same has_errors.
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    a => b = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in specify block", 3, "30.3"));
}

// §30.3, Syntax 30-1: a specify_block runs from `specify` to `endspecify`, and
// this source runs out before the keyword arrives, so Parser::Expect writes
// `expected 'endspecify', got EOF` for it. The specify block's report comes
// first because it is the innermost construct the source ran out of; the
// module's follows.
TEST(SpecifyBlock, MissingEndspecifyNames30_3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endspecify', got EOF", 3, "30.3"));
}

}  // namespace
