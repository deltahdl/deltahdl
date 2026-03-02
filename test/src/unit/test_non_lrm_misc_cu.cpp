// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection23, WildcardWithNamedOverrides) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .rst(global_rst), .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "rst");
  EXPECT_EQ(item->inst_ports[1].first, "clk");
}

TEST(ParserSection23, WildcardWithEmptyPort) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .unused());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "unused");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
}

}  // namespace
