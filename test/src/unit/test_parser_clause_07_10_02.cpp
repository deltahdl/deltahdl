// §7.10.2: Queue methods

#include "fixture_parser.h"

using namespace delta;

struct ParseResult7e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7e Parse(const std::string& src) {
  ParseResult7e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection7c, QueueInsertAndDelete) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(3);\n"
      "    q.insert(1, 2);\n"
      "    q.delete(0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
