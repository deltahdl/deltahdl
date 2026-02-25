// §6.24.1: Cast operator

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

// =============================================================================
// A.2.2.1 Net and variable types
// =============================================================================
// --- casting_type ---
// simple_type | constant_primary | signing | string | const
TEST(ParserA221, CastingTypeSimpleInt) {
  // simple_type: integer_type cast
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = int'(3.14); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeSigning) {
  // signing: signed'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = signed'(8'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeString) {
  // string: string'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin string s; s = string'(65); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeConst) {
  // const: const'(expr)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = const'(42); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeUserDefined) {
  // casting_type with user-defined type (simple_type: ps_type_identifier)
  // Note: constant_primary'(expr) cast (e.g., N'(val)) requires semantic
  // analysis to distinguish from sized literals — tested via type casts.
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  initial begin byte_t x; x = byte_t'(16'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
