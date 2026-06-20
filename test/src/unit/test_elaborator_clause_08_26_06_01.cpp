

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodConflict, SingleImplResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase1;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfBase2;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "class ClassExt implements IntfBase1, IntfBase2;\n"
             "  virtual function bit funcBase();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, ExtendsAndImplementsConflictOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IntfBase1;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfBase2;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "virtual class ClassBase;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "class ClassExt extends ClassBase implements IntfBase1, IntfBase2;\n"
      "  virtual function bit funcBase();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, InterfaceExtendsMultipleWithSameMethodOk) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "class D implements IC;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, IncompatibleReturnTypesError) {
  EXPECT_FALSE(
      ElabOk("interface class IntfBaseA;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfBaseB;\n"
             "  pure virtual function string funcBase();\n"
             "endclass\n"
             "class ClassA implements IntfBaseA, IntfBaseB;\n"
             "  virtual function bit funcBase();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, IncompatibleArgCountError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void f(int a);\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void f(int a, int b);\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void f(int a);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, IncompatibleArgTypesError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void f(int a);\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void f(string a);\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void f(int a);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict,
     InterfaceExtendsIncompatibleReturnTypesError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function int f();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, ImplConflictsWithInheritedBaseMethodError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function int f();\n"
             "endclass\n"
             "virtual class Base;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "class C extends Base implements IA;\n"
             "  virtual function int f();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodConflict, VirtualClassPrototypeResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "virtual class V implements IA, IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "class C extends V;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Claim A: the single resolving "implementation" need not be declared in the
// implementing class itself; a concrete virtual method inherited from a base
// class can simultaneously satisfy the same-named pure virtuals of every
// implemented interface.
TEST(InterfaceClassMethodConflict, InheritedConcreteMethodResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function bit f();\n"
             "endclass\n"
             "class Base;\n"
             "  virtual function bit f();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base implements IA, IB;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Claim A (cannot be resolved): the conflicting interface prototypes differ
// only in argument direction, so no single method can be a valid simultaneous
// implementation of both, and an error is required.
TEST(InterfaceClassMethodConflict, IncompatibleArgDirectionError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void f(input int a);\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void f(output int a);\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void f(input int a);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
