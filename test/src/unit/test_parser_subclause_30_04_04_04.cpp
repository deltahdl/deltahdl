#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(IfnoneConditionParsing, CoexistsWithIfPath) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if (en) (a => y) = 2;\n"
      "    ifnone (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IfnoneConditionParsing, ParallelPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(IfnoneConditionParsing, ErrorMissingPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got '='", 3, "30.4"));
}

TEST(IfnoneConditionParsing, ErrorEdgeSensitiveParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ifnone requires a simple path declaration", 3, "30.4.4.4"));
}

TEST(IfnoneConditionParsing, ErrorDataSourcePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ifnone requires a simple path declaration", 3, "30.4.4.4"));
}

TEST(IfnoneConditionParsing, FullConnectionPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, input b, output c);\n"
      "  specify\n"
      "    ifnone (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.condition, nullptr);
}

}  // namespace
