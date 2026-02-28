// §30.4.3: Edge-sensitive paths

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §30.3.1 Edge-sensitive paths
// =============================================================================
TEST_F(SpecifyTest, PosedgePath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (posedge clk => q) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* path = spec->specify_items[0];
  EXPECT_EQ(path->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(path->path.src_ports[0].name, "clk");
  EXPECT_EQ(path->path.dst_ports[0].name, "q");
}

TEST_F(SpecifyTest, NegedgePath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (negedge clk => q) = 8;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNegedge);
}

// =============================================================================
// A.7.2 data_source_expression with output polarity
// =============================================================================
// Edge-sensitive path with output-side polarity and data source
TEST(ParserA702, DataSourceWithOutputPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q + : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kPositive);
}

// Edge-sensitive path with negative output polarity and data source
TEST(ParserA702, DataSourceWithNegativeOutputPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q - : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNegative);
}

}  // namespace
