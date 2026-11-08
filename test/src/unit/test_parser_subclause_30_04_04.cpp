#include <gtest/gtest.h>

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

}  // namespace
