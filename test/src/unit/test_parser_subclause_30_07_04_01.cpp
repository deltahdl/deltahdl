#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;
namespace {

TEST(SpecifyBlockDeclParsing, PulsestyleOneventSingleOutput) {
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
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->path_outputs.size(), 1u);
  EXPECT_EQ(item->path_outputs[0].name, "out1");
}

TEST(SpecifyBlockDeclParsing, PulsestyleOneventMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1, out2, out3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->path_outputs.size(), 3u);
  EXPECT_EQ(item->path_outputs[0].name, "out1");
  EXPECT_EQ(item->path_outputs[1].name, "out2");
  EXPECT_EQ(item->path_outputs[2].name, "out3");
}

TEST(SpecifyBlockDeclParsing, PulsestyleOndetectSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->path_outputs.size(), 1u);
  EXPECT_EQ(item->path_outputs[0].name, "q");
}

TEST(SpecifyBlockDeclParsing, PulsestyleOndetectMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect a, b;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->path_outputs.size(), 2u);
  EXPECT_EQ(item->path_outputs[0].name, "a");
  EXPECT_EQ(item->path_outputs[1].name, "b");
}

TEST(SpecifyBlockDeclParsing, ErrorPulsestyleEmptyOutputList) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent ;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 3, "30.4"));
}

TEST(SpecifyBlockDeclParsing, ErrorPulsestyleMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.7.4.1"));
}

}  // namespace
