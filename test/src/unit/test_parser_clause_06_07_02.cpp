#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(Parser, NettypeUsedInDecl) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}

TEST(DataTypeParsing, NettypeUsedForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wT;\n"
              "  wT my_signal;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeArrayDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype logic [7:0] mynet;\n"
              "  mynet x [0:7];\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, ResolvedNettypeDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real r; bit [7:0] data; } T;\n"
              "  function T Tsum(input T driver[]);\n"
              "    Tsum.r = 0.0;\n"
              "    Tsum.data = 0;\n"
              "  endfunction\n"
              "  nettype T wTsum with Tsum;\n"
              "  wTsum w3;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, MultipleNettypeInstances) {
  auto r = Parse(
      "module m;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;

  ASSERT_GE(items.size(), 4u);
  EXPECT_EQ(items[1]->name, "a");
  EXPECT_EQ(items[2]->name, "b");
  EXPECT_EQ(items[3]->name, "c");
}

TEST(DataTypeParsing, UnresolvedNettypeDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wT;\n"
              "  wT w1;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeAlias) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real r; bit [7:0] data; } T;\n"
              "  function T Tsum(input T driver[]);\n"
              "    Tsum.r = 0.0;\n"
              "    Tsum.data = 0;\n"
              "  endfunction\n"
              "  nettype T wTsum with Tsum;\n"
              "  nettype wTsum nettypeid2;\n"
              "endmodule\n"));
}

}  // namespace
