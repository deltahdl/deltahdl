#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_Not) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not a);\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_PropertyNot) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not (a ##1 b));\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(ParserAnnexF, AnnexFPropertyNot) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a |-> b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserSection16, PropertyNegation) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not (a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyNegationStrong) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) not strong(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}
