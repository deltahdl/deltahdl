// §8.8: Typed constructor calls

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_new ---
// [ class_scope ] new [ ( list_of_arguments ) ]
// | new expression
TEST(ParserA24, ClassNewNoArgs) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// §8.8 — Typed constructor with parameterized scope: ClassName#(params)::new
TEST(ParserSection8, ParameterizedClassScopeNew) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls #(parameter int t = 12);\n"
      "    int a;\n"
      "    function new(int def = 42);\n"
      "      a = def - t;\n"
      "    endfunction\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = test_cls#(.t(23))::new(.def(41));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
