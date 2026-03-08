#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, ClassNewNoArgs) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection8, ParameterizedClassScopeNew) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls #(parameter int t = 12);\n"
      "    int a;\n"
      "    function new(int def = 42);\n"
      "      a = def - t;\n"
      "    endfunction\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = test_cls#(.t(23))::new(.def(41));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserA88, TypedConstructorNoArgs) {
  auto r = Parse(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = D::new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA88, TypedConstructorWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int x); super.new(x); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = D::new(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA88, ShallowCopy) {
  auto r = Parse(
      "class C;\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    a = new;\n"
      "    b = new a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA88, TypedConstructorNamedArgs) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function new(int val); x = val; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = C::new(.val(10));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA88, ParameterizedTypedConstructor) {
  auto r = Parse(
      "class E #(type T = int) extends C;\n"
      "  T x;\n"
      "  function new(T x_init);\n"
      "    super.new();\n"
      "    x = x_init;\n"
      "  endfunction\n"
      "endclass\n"
      "class C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = E#(.T(byte))::new(.x_init(5));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
