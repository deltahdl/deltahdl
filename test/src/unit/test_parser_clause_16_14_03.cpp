#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, ConcurrentAssertionItem_CoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, CoverSequence_Basic) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, CoverSequence_WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(ParserA210, CoverSequence_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover sequence (@(posedge clk) disable iff (rst) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CoverSequence_Kind) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kCoverSequence);
}

TEST(ParserA210, CoverProperty_WithPassStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(ParserA210, CoverSequence_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

TEST(ParserSection16, CoverPropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}
using VerifyParseTest = ProgramTestParse;

TEST(ParserSection16, Sec16_5_1_CoverPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

TEST(ParserSection16, Sec16_5_1_CoverPropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

TEST(ParserSection16, Sec16_5_1_CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

TEST(ParserSection16, Sec16_5_1_CoverSequenceWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

TEST(ParserSection16, ConcurrentCoverPropertyWithStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
}

TEST(ParserAnnexF, AnnexFCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

TEST(ParserSection39, CoverPropertyStatement) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a ##1 b);
    endmodule
  )"));
}

TEST(ParserSection40, CoverPropertyForAssertionCoverage) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a |-> ##[1:3] b);
    endmodule
  )"));
}

TEST(ParserA610, CoverPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA610, CoverSequenceModule) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA610, CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a) $display(\"covered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
}

}  // namespace
