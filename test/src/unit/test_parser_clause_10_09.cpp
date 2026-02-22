// §10.9: Assignment patterns

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// ===========================================================================
// §10.9-10.10: Assignment pattern evaluation
// ===========================================================================
TEST(Lexical, AssignmentPattern_DefaultZero) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial a = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Should parse without error.
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Positional) {
  auto r = Parse(
      "module top;\n"
      "  logic [3:0] a;\n"
      "  initial a = '{1, 0, 1, 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Named) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    logic [7:0] x;\n"
      "    x = '{default: 'x};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
