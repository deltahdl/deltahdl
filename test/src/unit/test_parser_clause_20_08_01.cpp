// §20.8.1: Integer math functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
}

struct ParseResult11e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11e Parse(const std::string& src) {
  ParseResult11e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection11, ConstExprSystemFuncInParam) {
  auto r = Parse(
      "module t;\n"
      "  parameter N = 16;\n"
      "  parameter BITS = $clog2(N);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
