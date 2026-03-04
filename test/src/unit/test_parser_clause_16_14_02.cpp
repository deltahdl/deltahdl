// §16.14.2: Assume statement

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.10 Production #4: assume_property_statement
// =============================================================================
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

// assume_property_statement with no action block
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

// --- Test helpers ---
// =============================================================================
// §16.5 Concurrent — assume property
// =============================================================================
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

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: assume property
// =============================================================================
// Assume property with a simple property expression.
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

// Assume property with a clocked implication.
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

// Assume property with else action.
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

// =============================================================================
// §16.5.1 Concurrent assert/assume/cover
// =============================================================================
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
  // assume property can also have callbacks placed on it
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, req, gnt;
      assume property (@(posedge clk) req |-> ##[1:3] gnt);
    endmodule
  )"));
}

// assume_property_statement
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

}  // namespace
