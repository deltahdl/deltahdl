// §13.8: Parameterized tasks and functions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §13.8: Parameterized class with type parameter.
TEST(ParserSection13, Sec13_8_TypeParameter) {
  EXPECT_TRUE(
      ParseOk("virtual class Converter#(parameter type T = int);\n"
              "  static function T identity(input T val);\n"
              "    return val;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Static method with return value used in expression.
TEST(ParserSection13, Sec13_8_StaticMethodInExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int val;\n"
              "  assign val = Utils#(8)::max_val() + 1;\n"
              "endmodule\n"));
}

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

// =============================================================================
// LRM §13.8 -- Parameterized tasks and functions
// =============================================================================
// §13.8: A virtual class with type parameters and a static method serves as
// a parameterized subroutine.
TEST(ParserSection13, Sec13_8_VirtualClassStaticTask) {
  auto r = Parse(
      "virtual class C#(parameter W = 8);\n"
      "  static task drive(input logic [W-1:0] data);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
  ASSERT_EQ(r.cu->classes[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params[0].first, "W");
}

// §13.8: Parameterized class with parameter used in local variable.
TEST(ParserSection13, Sec13_8_ParamInLocalVar) {
  EXPECT_TRUE(
      ParseOk("virtual class BitOps#(parameter W = 8);\n"
              "  static function logic [W-1:0] invert(input logic [W-1:0] x);\n"
              "    logic [W-1:0] mask;\n"
              "    mask = '1;\n"
              "    return x ^ mask;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Parameterized class with for loop using parameter as bound.
TEST(ParserSection13, Sec13_8_ForLoopWithParamBound) {
  EXPECT_TRUE(
      ParseOk("virtual class Popcount#(parameter W = 8);\n"
              "  static function int count_ones(input logic [W-1:0] val);\n"
              "    int cnt;\n"
              "    cnt = 0;\n"
              "    for (int i = 0; i < W; i++) begin\n"
              "      if (val[i]) cnt = cnt + 1;\n"
              "    end\n"
              "    return cnt;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Return type uses parameter.
TEST(ParserSection13, Sec13_8_ReturnTypeUsesParam) {
  EXPECT_TRUE(
      ParseOk("virtual class Pack#(parameter W = 8);\n"
              "  static function logic [2*W-1:0] double(\n"
              "      input logic [W-1:0] x);\n"
              "    return {x, x};\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Parameterized class with multiple methods calling each other.
TEST(ParserSection13, Sec13_8_MethodsCallEachOther) {
  EXPECT_TRUE(
      ParseOk("virtual class Math#(parameter W = 32);\n"
              "  static function logic [W-1:0] abs_val(\n"
              "      input logic signed [W-1:0] x);\n"
              "    return negate(x);\n"
              "  endfunction\n"
              "  static function logic [W-1:0] negate(\n"
              "      input logic signed [W-1:0] x);\n"
              "    return -x;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Assign result of parameterized call to variable.
TEST(ParserSection13, Sec13_8_AssignParamCallResult) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int result;\n"
              "  initial begin\n"
              "    result = Popcount#(32)::count_ones(32'hDEAD_BEEF);\n"
              "  end\n"
              "endmodule\n"));
}

// §13.8: Virtual class with only a static task (no function).
TEST(ParserSection13, Sec13_8_OnlyStaticTask) {
  auto r = Parse(
      "virtual class Printer#(parameter int ID = 0);\n"
      "  static task print();\n"
      "    $display(\"ID=%0d\", ID);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
// =============================================================================
// LRM section 13.8 -- Parameterized tasks and functions
// =============================================================================
TEST(ParserSection13, ParameterizedSubroutine_VirtualClassWithStaticMethod) {
  auto r = Parse(
      "virtual class C#(parameter DECODE_W = 8,\n"
      "                 parameter ENCODE_W = $clog2(DECODE_W));\n"
      "  static function logic [ENCODE_W-1:0] ENCODER_f\n"
      "      (input logic [DECODE_W-1:0] DecodeIn);\n"
      "    ENCODER_f = '0;\n"
      "    for (int i = 0; i < DECODE_W; i++) begin\n"
      "      if (DecodeIn[i]) begin\n"
      "        ENCODER_f = i[ENCODE_W-1:0];\n"
      "        break;\n"
      "      end\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_ClassScopeCall) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] encoder_in;\n"
      "  logic [2:0] encoder_out;\n"
      "  assign encoder_out = C#(8)::ENCODER_f(encoder_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_MultipleStaticMethods) {
  auto r = Parse(
      "virtual class C#(parameter W = 4);\n"
      "  static function logic [W-1:0] encode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  static function logic [W-1:0] decode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
