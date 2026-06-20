#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
}

TEST(IfnoneConditionParsing, ErrorEdgeSensitiveParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The simple-only restriction also rejects a data-source path description,
// which §30.4.3 permits without an edge identifier. This case carries no edge,
// so it observes the data_source branch of the restriction independently of the
// edge branch exercised by ErrorEdgeSensitiveParallel.
TEST(IfnoneConditionParsing, ErrorDataSourcePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(IfnoneConditionParsing, CoexistsWithEdgeSensitiveCompanion) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    ifnone (clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
