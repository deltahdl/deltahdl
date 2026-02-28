// §18.13.4: get_randstate()

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

// =============================================================================
// §18.13.4 get_randstate()
// =============================================================================
TEST(ParserSection18, GetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function string save_state();\n"
      "    return this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, GetRandstateAssignToVar) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string state;\n"
      "    p = process::self();\n"
      "    state = p.get_randstate();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
