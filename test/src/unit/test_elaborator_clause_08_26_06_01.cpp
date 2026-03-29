// §8.26.6.1

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Req: A method name conflict shall be resolved with a single method prototype
// or implementation that simultaneously provides an implementation for all pure
// virtual methods of the same name of any implemented interface class.

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

// Req: That method prototype or implementation shall also be a valid virtual
// method override (see 8.20) for any inherited method of the same name.

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

// Req: An interface class may inherit multiple methods with the same name.

TEST(InterfaceClassMethodConflict, InterfaceExtendsMultipleWithSameMethodOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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

// Req: Error when interface methods of the same name have incompatible return
// types, making simultaneous resolution impossible.

TEST(InterfaceClassMethodConflict, IncompatibleReturnTypesError) {
  EXPECT_FALSE(ElabOk(
      "interface class IntfBaseA;\n"
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

// Req: Error when interface methods of the same name have incompatible argument
// counts, making simultaneous resolution impossible.

TEST(InterfaceClassMethodConflict, IncompatibleArgCountError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
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

// Req: Error when interface methods of the same name have incompatible argument
// types, making simultaneous resolution impossible.

TEST(InterfaceClassMethodConflict, IncompatibleArgTypesError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
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

// Req: Error when an interface extends two interfaces whose same-named methods
// have incompatible signatures.

TEST(InterfaceClassMethodConflict, InterfaceExtendsIncompatibleReturnTypesError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
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

// Req: That method shall also be a valid virtual method override for any
// inherited method of the same name -- error when the implementing method's
// signature does not match the inherited base class method.

TEST(InterfaceClassMethodConflict, ImplConflictsWithInheritedBaseMethodError) {
  EXPECT_FALSE(ElabOk(
      "interface class IA;\n"
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

// Req: A virtual class shall define or inherit a pure virtual method prototype
// or virtual method implementation for each pure virtual method; a single
// prototype resolves same-named methods from multiple interfaces.

TEST(InterfaceClassMethodConflict, VirtualClassPrototypeResolvesConflict) {
  EXPECT_TRUE(ElabOk(
      "interface class IA;\n"
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

}  // namespace
