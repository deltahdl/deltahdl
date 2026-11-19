#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(StateDependentPathSyntax, IfGuardWrapsSimplePath) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if (en) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_NE(si->path.condition, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_FALSE(si->path.is_ifnone);
}

TEST(StateDependentPathSyntax, IfGuardWrapsEdgeSensitivePath) {
  auto r = Parse(
      "module m(input clk, input d, input en, output q);\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = (3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.delays.size(), 2u);
}

TEST(StateDependentPathSyntax, IfnoneWrapsSimplePath) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    ifnone (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(StateDependentPathSyntax, IfGuardWrapsFullConnectionSimplePath) {
  auto r = Parse(
      "module m(input a, input b, input en, output y);\n"
      "  specify\n"
      "    if (en) (a, b *> y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_FALSE(si->path.is_ifnone);
}

TEST(StateDependentPathSyntax, IfnoneWrapsFullConnectionSimplePath) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    ifnone (a, b *> y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(StateDependentPathSyntax, IfGuardRequiresParenthesizedCondition) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if en (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "30.4.4"));
}

ParseResult ParseStateDependentPath(const std::string& item) {
  return Parse(
      "module m(input a, b, clk, d, en, output y, q);\n"
      "  specify\n"
      "    " +
      item +
      "\n"
      "  endspecify\n"
      "endmodule\n");
}

TEST(StateDependentPathSyntax, IfGuardWrapsFullEdgeSensitivePath) {
  auto r = ParseStateDependentPath("if (en) (posedge clk *> (q, y : d)) = 1;");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(StateDependentPathSyntax, IfGuardWrapsParallelEdgePathWithDataSource) {
  auto r =
      ParseStateDependentPath("if (en) (negedge clk => (q -: d)) = (1, 2);");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNegative);
  ASSERT_EQ(si->path.delays.size(), 2u);
}

TEST(StateDependentPathSyntax, IfGuardWrapsDataPathWithNoEdgeIdentifier) {
  auto r = ParseStateDependentPath("if (en) (clk => (q : d)) = 1;");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(StateDependentPathSyntax, IfnoneTakesNoCondition) {
  auto r = ParseStateDependentPath("ifnone (en) (a => y) = 1;");
  EXPECT_TRUE(ReportedError(
      r.diags, "path joins its source to its destination with '=>' or '*>'", 3,
      "30.4.2"));
}

TEST(StateDependentPathSyntax, IfGuardRequiresAConditionExpression) {
  auto r = ParseStateDependentPath("if () (a => y) = 1;");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(StateDependentPathSyntax, IfGuardRequiresAPathDescription) {
  auto r = ParseStateDependentPath("if (en) = 5;");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got '='", 3, "30.4"));
}

TEST(StateDependentPathSyntax, IfGuardsDoNotNest) {
  auto r = ParseStateDependentPath("if (a) if (b) (a => y) = 1;");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got 'if'", 3, "30.4"));
}

TEST(StateDependentPathSyntax, IfGuardTakesNoElseBranch) {
  auto r = ParseStateDependentPath("if (en) (a => y) = 1; else (a => y) = 2;");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in specify block", 3, "30.3"));
}

}  // namespace
