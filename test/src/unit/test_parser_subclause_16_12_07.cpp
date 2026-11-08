#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

ModuleItem* FirstItemOfKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

TEST(AssertionSemanticsParsing, OverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonoverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, SequenceAntecedentOverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) (a ##1 b ##1 c) |-> (d ##1 e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonoverlapImplicationInAssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssumeProperty));
}

TEST(AssertionSemanticsParsing, OverlapImplicationInCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) start |-> busy);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kCoverProperty));
}

TEST(AssertionSemanticsParsing, ImplicationInNamedPropertyDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

TEST(AssertionSemanticsParsing, NestedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b |=> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing,
     ImplicationOperatorDrivesTemporalClassification) {
  const std::string_view kPlaceholder = "<property_spec>";

  auto overlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(overlap.cu, nullptr);
  auto* ov = FirstItemOfKind(overlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ov, nullptr);
  ASSERT_NE(ov->assert_expr, nullptr);
  EXPECT_EQ(ov->assert_expr->text, kPlaceholder);

  auto nonoverlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |=> b);\n"
      "endmodule\n");
  ASSERT_NE(nonoverlap.cu, nullptr);
  auto* no = FirstItemOfKind(nonoverlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(no, nullptr);
  ASSERT_NE(no->assert_expr, nullptr);
  EXPECT_EQ(no->assert_expr->text, kPlaceholder);

  auto boolean = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(boolean.cu, nullptr);
  auto* bl = FirstItemOfKind(boolean, ModuleItemKind::kAssertProperty);
  ASSERT_NE(bl, nullptr);
  ASSERT_NE(bl->assert_expr, nullptr);
  EXPECT_NE(bl->assert_expr->text, kPlaceholder);
}

}  // namespace
