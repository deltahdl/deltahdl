// §7.5.1: New[ ]

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

namespace {

// --- dynamic_array_new ---
// new [ expression ] [ ( expression ) ]
TEST(ParserA24, DynamicArrayNewSize) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  initial d = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayNewSizeAndInit) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  int src [10];\n"
      "  initial d = new[10](src);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayDeclWithNew) {
  auto r = Parse(
      "module m;\n"
      "  int d[] = new[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
