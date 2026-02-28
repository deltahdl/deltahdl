// §18.13.5: set_randstate()

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
// §18.13.5 set_randstate()
// =============================================================================
TEST(ParserSection18, SetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void restore_state(string state);\n"
      "    this.set_randstate(state);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SetRandstateInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string saved;\n"
      "    p = process::self();\n"
      "    saved = p.get_randstate();\n"
      "    p.set_randstate(saved);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
