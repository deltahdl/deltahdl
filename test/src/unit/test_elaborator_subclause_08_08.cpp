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

// §8.8: the specified type shall be assignment compatible with the target.
// An unrelated class as the constructor scope is therefore an error.
TEST(TypedConstructorCallElaboration, IncompatibleTypedConstructorRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class U; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = U::new;\n"
             "endmodule\n"));
}

// §8.8: the assignment-compatibility requirement holds regardless of whether
// arguments are passed to the typed constructor call.
TEST(TypedConstructorCallElaboration,
     IncompatibleTypedConstructorWithArgsRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class U;\n"
             "  function new(int x); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = U::new(1);\n"
             "endmodule\n"));
}

// §8.8: assignment compatibility is directional. A superclass type is not
// compatible with a subclass target, so naming the base class in a typed
// constructor call assigned to a derived handle is an error.
TEST(TypedConstructorCallElaboration,
     BaseTypeConstructorToDerivedTargetRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  D d;\n"
             "  initial d = C::new;\n"
             "endmodule\n"));
}

// §8.8: the assignment-compatibility rule also governs a typed constructor call
// initializing a module-scope declaration (`C c = U::new;` at module level,
// outside any procedural block). An unrelated specified type is rejected there
// just as in a procedural assignment or a block-local declaration.
TEST(TypedConstructorCallElaboration, IncompatibleModuleLevelDeclInitRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class U; endclass\n"
             "module m;\n"
             "  C c = U::new;\n"
             "endmodule\n"));
}

// §8.8: the assignment-compatibility rule applies to a typed constructor call
// used as a declaration initializer, not only a procedural assignment. A
// compatible derived type in a block-local `C c = D::new;` declaration
// elaborates.
TEST(TypedConstructorCallElaboration, BlockLocalDeclInitElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c = D::new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.8: conversely, an unrelated (incompatible) type named in a typed
// constructor call that initializes a block-local declaration is rejected --
// the compatibility rule is enforced on the declaration-initializer form.
TEST(TypedConstructorCallElaboration, IncompatibleBlockLocalDeclInitRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class U; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c = U::new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.8: the directional nature of the rule also holds for a declaration
// initializer -- a base type initializing a derived-typed local is rejected.
TEST(TypedConstructorCallElaboration, BaseToDerivedBlockLocalDeclInitRejected) {
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    D d = C::new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.8: a type several levels down the inheritance chain is still assignment
// compatible with a base-class target, so the typed constructor call is
// accepted across more than one extension step.
TEST(TypedConstructorCallElaboration,
     MultiLevelDerivedTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "class E extends D; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = E::new;\n"
             "endmodule\n"));
}

}  // namespace
