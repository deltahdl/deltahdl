#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh501, Sec5_1_WhitespaceTabDelimiter) {

  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tendmodule"));
}

TEST(ParserCh501, Sec5_1_WhitespaceNewlineDelimiter) {

  EXPECT_TRUE(
      ParseOk("module\n"
              "t\n"
              ";\n"
              "logic\n"
              "a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_WhitespaceSpaceDelimiter) {

  EXPECT_TRUE(ParseOk("module t ; logic a ; endmodule"));
}

TEST(ParserCh501, Sec5_1_WhitespaceInsideStringPreserved) {

  auto r = Parse(
      "module m;\n"
      "  initial $display(\"  hello   world  \");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);

  EXPECT_NE(stmt->expr->args[0]->text.find("  hello   world  "),
            std::string_view::npos);
}

TEST(ParserCh501, Sec5_1_MultipleConsecutiveWhitespace) {

  EXPECT_TRUE(
      ParseOk("module   \t\t   t  \n\n\n ;   logic   a  ;   endmodule"));
}

TEST(ParserCh501, Sec5_1_EmptyModuleMinimalWhitespace) {

  EXPECT_TRUE(ParseOk("module t;endmodule"));
}

TEST(ParserCh501, Sec5_1_EmptyModuleExcessiveWhitespace) {

  EXPECT_TRUE(
      ParseOk("  \t\n  module  \t  t  \n  ;  \n\n\t  endmodule  \n\n  "));
}

TEST(ParserCh501, Sec5_1_OperatorFollowedByNumber) {

  auto r = Parse(
      "module m;\n"
      "  initial x = a+1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->rhs->int_val, 1u);
}

TEST(ParserCh501, Sec5_1_MixedTokensNoWhitespace) {

  EXPECT_TRUE(ParseOk("module m;logic a;assign a=1'b0;endmodule"));
}

TEST(ParserCh501, Sec5_1_MultipleStatementsOnOneLine) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = 1; y = 2; z = 3; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 3u);
}

TEST(ParserCh501, Sec5_1_StatementSpanningManyLines) {

  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  assign\n"
      "    a\n"
      "    =\n"
      "    b\n"
      "    +\n"
      "    c\n"
      "    +\n"
      "    d\n"
      "    ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

  ASSERT_GE(r.cu->modules[0]->items.size(), 5u);
  auto* assign_item = r.cu->modules[0]->items[4];
  EXPECT_EQ(assign_item->kind, ModuleItemKind::kContAssign);
}

TEST(ParserCh501, Sec5_1_TabCharactersAsWhitespace) {

  EXPECT_TRUE(
      ParseOk("module\tm;\n"
              "\tlogic\ta;\n"
              "\tassign\ta\t=\t1'b1;\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_CarriageReturnLineFeed) {

  EXPECT_TRUE(
      ParseOk("module t;\r\n"
              "  logic a;\r\n"
              "endmodule\r\n"));
}

TEST(ParserCh501, Sec5_1_EmptyCuWhitespaceOnly) {

  auto r = Parse("   \t\n\n  \t  ");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

}
