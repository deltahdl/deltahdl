#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- State-dependent path declarations ---

TEST(SpecifyPathParsing, StateDependentIfSimpleFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
}

TEST(SpecifyPathParsing, StateDependentIfEdgeSensitive) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
}

TEST(SpecifyPathParsing, StateDependentIfnoneSimple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
}

TEST(SpecifyPathParsing, ConditionalPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(SpecifyPathParsing, ConditionalFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, b, en, output y);\n"
              "  specify\n"
              "    if (en) (a, b *> y) = 10;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(SpecifyPathParsing, IfnonePath) {
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

// --- Polarity with state-dependent wrappers ---

TEST(SpecifyPathParsing, PolarityWithConditionalPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (sel) (a + => b) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// --- Edge cases and combinations ---

TEST(SpecifyPathParsing, IfnoneFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
}

TEST(SpecifyPathParsing, StateDependentIfEdgeSensitiveFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

// --- Error conditions ---

TEST(SpecifyPathParsing, ErrorPathDeclMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorIfnoneMissingPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
