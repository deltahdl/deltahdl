#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, AssumeProperty_WithElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req)\n"
      "    $display(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(ParserA210, AssumeProperty_NoActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, AssumePropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}
using VerifyParseTest = ProgramTestParse;

TEST(ParserSection16, Sec16_5_1_AssumePropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(ParserSection16, Sec16_5_1_AssumePropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(ParserSection16, Sec16_5_1_AssumePropertyElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) en |-> ready)\n"
      "    else $error(\"assumption violated\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_EQ(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(ParserSection16, ConcurrentAssumePropertyWithAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt)\n"
      "    else $error(\"assumption failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(ParserAnnexF, AnnexFAssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

TEST(ParserSection39, AssumePropertyStatement) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, req, gnt;
      assume property (@(posedge clk) req |-> ##[1:3] gnt);
    endmodule
  )"));
}

TEST(ParserA610, AssumePropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assume property (req |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

}
