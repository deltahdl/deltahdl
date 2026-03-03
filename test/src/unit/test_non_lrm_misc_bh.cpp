// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection6, StringComparison) {
  // String comparison operators
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string a, b;\n"
              "  initial begin\n"
              "    a = \"abc\";\n"
              "    b = \"def\";\n"
              "    if (a == b) $display(\"equal\");\n"
              "    if (a != b) $display(\"not equal\");\n"
              "    if (a < b) $display(\"less\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, MultipleStringDecls) {
  auto r = Parse(
      "module m;\n"
      "  string x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

}  // namespace
