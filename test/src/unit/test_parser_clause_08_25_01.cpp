// §8.25.1: Class scope resolution operator for parameterized classes

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_type ---
// ps_class_identifier [param] { :: class_identifier [param] }
TEST(ParserA221, ClassTypeParameterized) {
  auto r = Parse(
      "class param_cls #(type T = int);\n"
      "  typedef T value_t;\n"
      "endclass\n"
      "module m; param_cls#(int)::value_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// §13.8: Class scope resolution call with parameterization.
TEST(ParserSection13, Sec13_8_ScopeCallParsesAsExpr) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] d;\n"
      "  logic [2:0] e;\n"
      "  assign e = Codec#(8)::encode(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Two different specializations in the same module.
TEST(ParserSection13, Sec13_8_TwoSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a4;\n"
      "  logic [15:0] a16;\n"
      "  logic [1:0] r4;\n"
      "  logic [3:0] r16;\n"
      "  assign r4  = C#(4)::ENCODER_f(a4);\n"
      "  assign r16 = C#(16)::ENCODER_f(a16);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Specialization with multiple parameter overrides.
TEST(ParserSection13, Sec13_8_MultiParamSpecialization) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [31:0] result;\n"
      "  assign result = Xform#(16, 32, 2)::widen(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Call to parameterized class with type parameter override.
TEST(ParserSection13, Sec13_8_TypeParamOverrideCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  assign y = Converter#(logic [7:0])::identity(x);\n"
              "endmodule\n"));
}

// §13.8: Chained call — result of parameterized call used as argument.
TEST(ParserSection13, Sec13_8_ChainedParameterizedCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a, b, c;\n"
              "  assign c = Arith#(8)::add(a, Arith#(8)::add(a, b));\n"
              "endmodule\n"));
}

}  // namespace
