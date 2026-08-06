#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassAllowedContent, InterfaceClassTypeAndParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  typedef int my_int;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassNonPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassDataMemberError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassMultiplePureVirtualsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  pure virtual function int bar();\n"
             "  pure virtual task do_stuff();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassImplementsInterface, ConcreteMethodSatisfiesPureVirtual) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassImplementsInterface, NonVirtualMethodDoesNotImplement) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, MissingPureVirtualImplementation) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, AllPureVirtualMethodsImplemented) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  virtual function bit funcB();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, MultipleInterfacesAllMethodsImplemented) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void funcA();\n"
             "  endfunction\n"
             "  virtual function void funcB();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, MultipleInterfacesMissingOneMethodError) {
  EXPECT_FALSE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void funcA();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, ParameterDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int WIDTH = 8;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26 forbids constraint blocks, covergroups and nested classes alike in an
// interface class. The constraint-block and covergroup halves are stated again
// by §8.26.9 and are covered in test_elaborator_subclause_08_26_09.cpp; the
// nested-class half has no subclause of its own and is covered here.
TEST(InterfaceClassAllowedContent, NestedClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  class Nested;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassNestedInInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class Outer;\n"
             "  pure virtual function void foo();\n"
             "  interface class Inner;\n"
             "    pure virtual function void bar();\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, SubclassInheritsInterfaceImplementation) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "class C extends B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26 C9: an interface-class-typed handle may reference an instance of a
// class that declares (via 'implements') that it implements the interface.
TEST(InterfaceClassHandleAssign, ImplementingClassAssignableToInterfaceHandle) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IC ih;\n"
             "    C c;\n"
             "    ih = c;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26 C9: merely defining every pure-virtual method is not sufficient; a
// class that does not declare 'implements' cannot be assigned to an
// interface-class handle.
TEST(InterfaceClassHandleAssign,
     NonImplementingClassNotAssignableToInterfaceHandle) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "class D;\n"
             "  virtual function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IC ih;\n"
             "    D d;\n"
             "    ih = d;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26 C5: an interface class may inherit from another interface class via
// 'extends'.
TEST(InterfaceClassInheritance, InterfaceClassExtendsInterfaceClassOk) {
  EXPECT_TRUE(
      ElabOk("interface class IB;\n"
             "  pure virtual function void g();\n"
             "endclass\n"
             "interface class IC extends IB;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26 C5: an interface class shall not extend an ordinary (non-interface)
// class.
TEST(InterfaceClassInheritance, InterfaceClassExtendsRegularClassError) {
  EXPECT_FALSE(
      ElabOk("class SomeRegularClass;\n"
             "endclass\n"
             "interface class IC extends SomeRegularClass;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.1 lets a class be declared wherever a data declaration may appear, so the
// three below write theirs inside a module. Every other case in this file
// declares at compilation-unit scope, which is the placement that cannot tell a
// rule enforced everywhere from a rule enforced at the top of a file.
TEST(InterfaceClassAllowedContent, InterfaceClassInsideAModuleDataMemberError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  interface class IC;\n"
             "    int data;\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements,
     MissingPureVirtualImplementationInsideAModuleError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  interface class IC;\n"
             "    pure virtual function void foo();\n"
             "  endclass\n"
             "  class C implements IC;\n"
             "  endclass\n"
             "endmodule\n"));
}

// The control the two above need: the same placement written correctly stays
// legal, so neither error can be passing because a class inside a module is
// rejected out of hand.
TEST(InterfaceClassImplements, ImplementationInsideAModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class IC;\n"
             "    pure virtual function void foo();\n"
             "  endclass\n"
             "  class C implements IC;\n"
             "    virtual function void foo();\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
