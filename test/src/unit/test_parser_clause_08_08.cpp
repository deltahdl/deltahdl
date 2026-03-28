#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallParsing, ParameterizedClassScopeNew) {
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

TEST(TypedConstructorCallParsing, TypedConstructorNoArgs) {
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

TEST(TypedConstructorCallParsing, TypedConstructorWithArgs) {
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

TEST(TypedConstructorCallParsing, TypedConstructorNamedArgs) {
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

TEST(TypedConstructorCallParsing, ParameterizedTypedConstructor) {
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

TEST(TypedConstructorCallParsing, TypedConstructorAstStructure) {
  auto r = Parse(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = D::new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->text, "new");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

TEST(TypedConstructorCallParsing, TypedConstructorWithArgsAstStructure) {
  auto r = Parse(
      "class C; endclass\n"
      "class D extends C;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = D::new(7);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->args.size(), 1u);
}

TEST(TypedConstructorCallParsing, TypedConstructorInDeclaration) {
  auto r = Parse(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module m;\n"
      "  C c = D::new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypedConstructorCallParsing, TypedConstructorSameType) {
  auto r = Parse(
      "class C;\n"
      "  function new(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = C::new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypedConstructorCallParsing, TypedConstructorMultipleArgs) {
  auto r = Parse(
      "class C;\n"
      "  int a, b, c;\n"
      "  function new(int x, int y, int z);\n"
      "    a = x; b = y; c = z;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C obj;\n"
      "  initial obj = C::new(1, 2, 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->args.size(), 3u);
}

TEST(TypedConstructorCallParsing, ParameterizedWithMultipleParams) {
  auto r = Parse(
      "class C; endclass\n"
      "class F #(type T = int, int N = 4) extends C;\n"
      "  function new(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = F#(.T(byte), .N(8))::new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
