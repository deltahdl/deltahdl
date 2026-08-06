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

// Claim B admits any SIMPLE module path under ifnone. §30.4.2 defines two
// simple-path connection forms: parallel (=>), exercised by ParallelPath, and
// full (*>). A full-connection ifnone is still a simple path, so it must parse
// cleanly and be flagged as ifnone. This covers the second admitted syntactic
// form of the accept side, distinct from the parallel form.
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
