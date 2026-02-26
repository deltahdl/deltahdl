// §16.12.8: Implies and iff properties

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

// property_expr ::= property_expr implies property_expr
TEST(ParserA210, PropertyExpr_Implies) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a implies b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr iff property_expr
TEST(ParserA210, PropertyExpr_Iff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a iff b);\n"
              "endmodule\n"));
}

}  // namespace
