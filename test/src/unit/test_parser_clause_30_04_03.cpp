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

}  // namespace
