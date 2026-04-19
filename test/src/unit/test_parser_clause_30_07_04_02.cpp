#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(SpecifyBlockDeclParsing, ShowcancelledSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(SpecifyBlockDeclParsing, NoshowcancelledSingleOutput) {
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
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(SpecifyBlockDeclParsing, NoshowcancelledMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1, out2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
}

TEST(SpecifyBlockDeclParsing, ShowcancelledMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1, out2, out3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(SpecifyBlockDeclParsing, ErrorShowcancelledMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyBlockDeclParsing, ErrorNoshowcancelledMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
