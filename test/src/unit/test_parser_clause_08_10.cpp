// §8.10: Static methods

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// §13.8: Virtual class with both static function and static task.
TEST(ParserSection13, Sec13_8_MixedStaticFuncAndTask) {
  auto r = Parse(
      "virtual class Utils#(parameter N = 4);\n"
      "  static function int max_val();\n"
      "    return (1 << N) - 1;\n"
      "  endfunction\n"
      "  static task report();\n"
      "    $display(\"N=%0d\", N);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 2u);
}

// §13.8: Static method with no arguments.
TEST(ParserSection13, Sec13_8_StaticMethodNoArgs) {
  auto r = Parse(
      "virtual class Constants#(parameter N = 32);\n"
      "  static function int zero();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §13.8: Static method with multiple arguments of parameterized width.
TEST(ParserSection13, Sec13_8_MultiArgParameterizedWidth) {
  EXPECT_TRUE(
      ParseOk("virtual class Arith#(parameter W = 16);\n"
              "  static function logic [W-1:0] add(\n"
              "      input logic [W-1:0] a,\n"
              "      input logic [W-1:0] b);\n"
              "    return a + b;\n"
              "  endfunction\n"
              "endclass\n"));
}

}  // namespace
