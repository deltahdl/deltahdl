// §8.25: Parameterized classes

#include "fixture_parser.h"

using namespace delta;

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// §8.5 — Parameterized classes
TEST(ParserSection8, ParameterizedClass) {
  auto r = Parse(
      "class stack #(parameter int DEPTH = 8);\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "stack");
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassMultipleParams) {
  auto r = Parse(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "WIDTH");
  EXPECT_EQ(cls->params[1].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassTypeParam) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

// §8.5 — Parameterized class with extends
TEST(ParserSection8, ParameterizedClassExtendsName) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  EXPECT_EQ(cls->name, "Derived");
  EXPECT_EQ(cls->base_class, "Base");
}

TEST(ParserSection8, ParameterizedClassExtendsParams) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "N");
}

// §8.5 — Parameterized class inside module (the sv-tests TIMEOUT case)
TEST(ParserSection8, ParameterizedClassInsideModuleName) {
  auto r = Parse(
      "module class_tb;\n"
      "  class test_cls #(parameter a = 12);\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  EXPECT_EQ(cls->name, "test_cls");
}

TEST(ParserSection8, ParameterizedClassInsideModuleParams) {
  auto r = Parse(
      "module class_tb;\n"
      "  class test_cls #(parameter a = 12);\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "a");
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

// §13.8: Multiple parameters with defaults.
TEST(ParserSection13, Sec13_8_MultipleParamsWithDefaults) {
  auto r = Parse(
      "virtual class Codec#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = $clog2(IN_W));\n"
      "  static function logic [OUT_W-1:0] encode(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    encode = '0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->params[0].first, "IN_W");
  EXPECT_EQ(r.cu->classes[0]->params[1].first, "OUT_W");
}

// §13.8: Three parameters with complex expressions.
TEST(ParserSection13, Sec13_8_ThreeParams) {
  auto r = Parse(
      "virtual class Xform#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = IN_W * 2,\n"
      "                     parameter DEPTH = 4);\n"
      "  static function logic [OUT_W-1:0] widen(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    return {DEPTH{data}};\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 3u);
}

// §13.8: Parameterized class with no default parameter value.
TEST(ParserSection13, Sec13_8_NoDefaultParam) {
  auto r = Parse(
      "virtual class Shifter#(parameter int AMOUNT);\n"
      "  static function logic [31:0] left(input logic [31:0] val);\n"
      "    return val << AMOUNT;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// §13.8: Parameterized class extending another class.
TEST(ParserSection13, Sec13_8_ClassExtends) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  virtual function void display();\n"
              "  endfunction\n"
              "endclass\n"
              "virtual class Derived#(parameter N = 1) extends Base;\n"
              "  static function int count();\n"
              "    return N;\n"
              "  endfunction\n"
              "endclass\n"));
}

// =============================================================================
// §8.25 -- Parameterized classes (additional tests)
// =============================================================================
TEST(ParserSection8, ParameterizedClassSpecialization) {
  auto r = Parse(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "endclass\n"
      "module m;\n"
      "  vector #(10) vten;\n"
      "  vector #(.size(2)) vtwo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection8, ParameterizedClassStackType) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "  function void push(T a);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

TEST(ParserSection8, ParameterizedClassDefaultInstantiation) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "endclass\n"
      "module m;\n"
      "  stack is_default;\n"
      "  stack #(real) rs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// Class with type parameter used as member type.
TEST(ParserSection8, TypeParameterClassMember) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T value;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

}  // namespace
