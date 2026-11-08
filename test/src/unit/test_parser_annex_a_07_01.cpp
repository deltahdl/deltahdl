#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

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

TEST(SpecifyBlockDeclParsing, PulsestyleListOfPathOutputsTakesDescriptors) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q[3], bus[7:0], \\q-1 , intf.p;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  const auto& outs = spec->specify_items[0]->path_outputs;
  ASSERT_EQ(outs.size(), 4u);
  EXPECT_EQ(outs[0].name, "q");
  EXPECT_EQ(outs[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(outs[1].name, "bus");
  EXPECT_EQ(outs[1].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(outs[2].name, "q-1");
  EXPECT_EQ(outs[3].interface_name, "intf");
  EXPECT_EQ(outs[3].name, "p");
}

TEST(SpecifyBlockDeclParsing, ShowcancelledListOfPathOutputsTakesDescriptors) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled q[0], \\q-1 ;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
  const auto& outs = spec->specify_items[0]->path_outputs;
  ASSERT_EQ(outs.size(), 2u);
  EXPECT_EQ(outs[0].name, "q");
  EXPECT_EQ(outs[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(outs[1].name, "q-1");
  EXPECT_EQ(outs[1].range_kind, SpecifyRangeKind::kNone);
}

TEST(SpecifyBlockDeclParsing, PulsestyleBraceListRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent {a, b};\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "path terminals are listed with commas alone; a "
                            "concatenation is no specify terminal",
                            3, "A.7.3"));
}

TEST(SpecifyBlockDeclParsing, PulsestyleDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.7.4.1"));
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

TEST(SpecifyBlockDeclParsing, ShowcancelledDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.7.4.2"));
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
}

TEST(SpecifyBlockDeclParsing, SpecifyBlockMissingEndspecifyRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endspecify', got EOF", 3, "30.3"));
}

}  // namespace
