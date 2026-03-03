// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// --- Streaming operator with type-sized slice (§11.4.14) ---
TEST(ParserSection11, StreamingWithTypedSlice) {
  auto r = Parse(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  initial b = {<< byte {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Tagged union expressions (§11.9) ---
TEST(ParserSection11, TaggedUnionExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int a;\n"
      "    a = tagged Invalid;\n"
      "    a = tagged Valid (42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
