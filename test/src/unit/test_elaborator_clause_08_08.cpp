#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallElaboration, BasicTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = D::new;\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function new(int v); x = v; endfunction\n"
             "endclass\n"
             "class D extends C;\n"
             "  function new(int v); super.new(v); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = D::new(42);\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorNamedArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function new(int val); x = val; endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = C::new(.val(10));\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorSameTypeElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function new(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = C::new;\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, ParameterizedTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class E #(type T = int) extends C;\n"
             "  T x;\n"
             "  function new(T x_init);\n"
             "    super.new();\n"
             "    x = x_init;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = E#(.T(byte))::new(.x_init(5));\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorInDeclarationElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C c = D::new;\n"
             "endmodule\n"));
}

}  // namespace
