// §18.5.6: if–else constraints

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult19 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult19 Parse(const std::string& src) {
  ParseResult19 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection18b, DistInsideIfConstraint) {
  // Distribution inside a conditional constraint block
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) {\n"
      "      x dist {[0:10] := 1};\n"
      "    } else {\n"
      "      x dist {[100:200] := 1};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
