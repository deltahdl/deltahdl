// §23.11: Binding auxiliary code to scopes or instances

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

// Bind with parameterized instantiation.
TEST(SourceText, BindDirectiveParameterized) {
  auto r = Parse("bind target_mod my_checker #(8) chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto* inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

// Bind stores source location.
TEST(SourceText, BindDirectiveHasSourceLoc) {
  auto r = Parse("bind target_mod chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->loc.line, 0u);
}

}  // namespace
