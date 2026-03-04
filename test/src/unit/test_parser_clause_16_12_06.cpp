// §16.12.6: If-else property

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// property_expr ::= if (...) property_expr [else property_expr]
TEST(ParserA210, PropertyExpr_IfElse) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  assert property (@(posedge clk)\n"
                      "    if (mode) a |-> b else c |-> d);\n"
                      "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_IfNoElse) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  assert property (@(posedge clk)\n"
                      "    if (mode) a |-> b);\n"
                      "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// Assert property with if-else inside property expression.
TEST(ParserSection16, Sec16_5_1_PropertyIfElse) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  assert property (\n"
                      "    @(posedge clk)\n"
                      "    if (mode) a |-> b\n"
                      "    else a |-> c);\n"
                      "endmodule\n"));
}

bool HasItemKind(ParseResult &r, ModuleItemKind kind) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == kind)
      return true;
  }
  return false;
}

// --- F.15: Property if-else ---
TEST(ParserAnnexF, AnnexFPropertyIfElse) {
  auto r = Parse("module m;\n"
                 "  property p_cond;\n"
                 "    @(posedge clk) if (mode) a |-> b; else c |-> d;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// --- Test helpers ---
// =============================================================================
// §16.14.6.2 Property if-else
// =============================================================================
TEST(ParserSection16, PropertyIfElse) {
  auto r = Parse("module m;\n"
                 "  assert property (\n"
                 "    @(posedge clk)\n"
                 "    if (mode) a |-> b\n"
                 "    else a |-> c);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfWithoutElse) {
  auto r = Parse("module m;\n"
                 "  assert property (\n"
                 "    @(posedge clk)\n"
                 "    if (en) a |-> ##[1:3] b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, PropertyIfElseInDecl) {
  auto r = Parse("module m;\n"
                 "  property p1;\n"
                 "    @(posedge clk)\n"
                 "    if (sel)\n"
                 "      req |-> ##1 ack\n"
                 "    else\n"
                 "      req |-> ##2 ack;\n"
                 "  endproperty\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

} // namespace
