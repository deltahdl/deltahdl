// §19.7: Specifying coverage options

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

  return nullptr;
}

namespace {

// =============================================================================
// §A.2.11 Production #2: coverage_spec_or_option
// =============================================================================
TEST(ParserA211, CoverageSpecOrOption_Option) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 128;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #3: coverage_option
// =============================================================================
TEST(ParserA211, CoverageOption_OptionMember) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.weight = 2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageOption_Goal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.goal = 90;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
