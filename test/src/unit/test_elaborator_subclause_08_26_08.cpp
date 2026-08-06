#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodDefaults, MatchingDefaultValuesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MultipleDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a = 0, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a = 0, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MixedDefaultAndNonDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ImplementorMissingDefaultError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ImplementorAddsUnexpectedDefaultError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MultipleImplementorsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int get(int a = 10);\n"
             "endclass\n"
             "class A implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, InheritedInterfaceDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class Base;\n"
             "  pure virtual function int foo(int a = 3);\n"
             "endclass\n"
             "interface class Derived extends Base;\n"
             "endclass\n"
             "class C implements Derived;\n"
             "  virtual function int foo(int a = 3);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MismatchedDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 10);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MismatchedSecondDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a = 0, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a = 0, int b = 99);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, NonConstantDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = x);\n"
             "endclass\n"
             "module m;\n"
             "  int x = 5;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ConstantExpressionDefaultValueOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 3 + 4);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 3 + 4);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The default value must be the same for *every* implementing class; a second
// implementor whose default differs from the interface prototype is rejected.
TEST(InterfaceClassMethodDefaults, SecondImplementorMismatchedDefaultError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int get(int a = 10);\n"
             "endclass\n"
             "class A implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function int get(int a = 20);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Equality is judged on the evaluated constant, not the source text: a literal
// default and a syntactically different expression of equal value agree.
TEST(InterfaceClassMethodDefaults, EquivalentConstantExpressionDefaultsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 2 + 3);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Conversely, two constant expressions that evaluate to different values are a
// mismatch even though both are well-formed constant expressions.
TEST(InterfaceClassMethodDefaults,
     ConstantExpressionDefaultValueMismatchError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 2 + 2);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// A default expression may be any constant expression of 11.2.1, not only a
// bare literal. Here a compilation-unit localparam supplies the default; the
// interface prototype admits it as a constant expression and it agrees with the
// implementor's identical reference.
TEST(InterfaceClassMethodDefaults, LocalparamConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("localparam int K = 5;\n"
             "interface class IC;\n"
             "  pure virtual function int foo(int a = K);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = K);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Because the default is evaluated in the scope containing the subroutine
// declaration, a value parameter of the interface class itself -- visible by
// its bare name inside the class body -- is a valid constant-expression
// default.
TEST(InterfaceClassMethodDefaults, ClassParameterConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC #(int P = 7);\n"
             "  pure virtual function int foo(int a = P);\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// A constant-expression default may also name a compilation-unit `parameter` --
// a distinct 11.2.1 constant form from a bare literal or a localparam. The
// interface prototype admits it and it agrees with the implementor's identical
// reference.
TEST(InterfaceClassMethodDefaults, ParameterConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("parameter int P = 8;\n"
             "interface class IC;\n"
             "  pure virtual function int foo(int a = P);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = P);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The "same value for every implementor" rule folds a named-constant default to
// its value before comparing: an implementor whose literal default differs from
// the interface's localparam-valued default is a mismatch.
TEST(InterfaceClassMethodDefaults, LocalparamDefaultValueMismatchError) {
  EXPECT_FALSE(
      ElabOk("localparam int K = 5;\n"
             "interface class IC;\n"
             "  pure virtual function int foo(int a = K);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 6);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
