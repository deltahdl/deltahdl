// §8.23: Class scope resolution operator ::

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
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

// --- class_scope ---
// class_type ::
TEST(ParserA221, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
