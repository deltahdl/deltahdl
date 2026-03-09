#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) (a |-> b));\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyAndSequenceDeclsTogether) {
  auto r = Parse(
      "module m;\n"
      "  property p; a; endproperty\n"
      "  sequence s; b; endsequence\n"
      "  assert property (p);\n"
      "  cover sequence (s);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl),
      nullptr);
}

TEST(ParserA210, SequenceActualArg_EventExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(posedge x, y));\n"
              "endmodule\n"));
}

}  // namespace
