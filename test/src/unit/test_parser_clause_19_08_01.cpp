// §19.8.1: Overriding the built-in sample method

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

TEST(ParserA211, CovergroupDecl_WithSampleFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int x, bit y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_WithFunctionSample) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(bit [3:0] val);\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
