

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassInheritance, InterfaceExtendsInterface) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B extends A;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, InterfaceImplementsInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B implements A;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// An interface class is barred from the 'implements' mechanism entirely: it may
// not implement a regular class (nor a virtual class) any more than it may
// implement another interface class. Inheritance for an interface class is
// exclusively through 'extends' targeting interface classes.
TEST(InterfaceClassImplements, InterfaceImplementsClassError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "endclass\n"
             "interface class IC implements Base;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The "or virtual class" arm of the same prohibition: an interface class naming
// a virtual class after 'implements' is rejected just as a regular-class target
// is. The bar is on an interface class using 'implements' at all, so the target
// being virtual rather than plain does not change the outcome.
TEST(InterfaceClassImplements, InterfaceImplementsVirtualClassError) {
  EXPECT_FALSE(
      ElabOk("virtual class VBase;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "interface class IC implements VBase;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassInheritance, InterfaceExtendsClassError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "endclass\n"
             "interface class IC extends Base;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsVsImplementsRestrictions, ClassExtendsInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C extends IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsAndImplements, ClassExtendsBaseImplementsInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class Base;\n"
             "endclass\n"
             "class Child extends Base implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, SingleInterfaceImplementationOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  pure virtual function void funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  virtual function void funcC();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "class C implements A, B;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, InheritedMethodSatisfiesInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcBase();\n"
             "  pure virtual function bit funcExt();\n"
             "endclass\n"
             "class BaseClass;\n"
             "  virtual function bit funcBase();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class ExtClass extends BaseClass implements IntfClass;\n"
             "  virtual function bit funcExt();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassExtends, MultipleBaseInterfaceClasses) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "interface class GetImp;\n"
             "  pure virtual function void get();\n"
             "endclass\n"
             "interface class PutGetIntf extends PutImp, GetImp;\n"
             "  pure virtual function void both();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, NonVirtualMethodDoesNotSatisfyInterface) {
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

TEST(InterfaceClassInheritance, InterfaceExtendsVirtualClassError) {
  EXPECT_FALSE(
      ElabOk("virtual class VBase;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class IC extends VBase;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsVsImplementsRestrictions, VirtualClassExtendsInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "virtual class VC extends IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsVsImplementsRestrictions, ClassImplementsNonInterfaceError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "endclass\n"
             "class C implements Base;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, VirtualClassImplementsInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "virtual class VC implements IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.2: the 'implements' target must be an interface class. A *virtual*
// class is still a class, not an interface class, so naming one after
// 'implements' is rejected exactly as a regular class would be — this covers
// the "or virtual class" input form of that prohibition, which the plain-class
// case above does not exercise.
TEST(ExtendsVsImplementsRestrictions, ClassImplementsVirtualClassError) {
  EXPECT_FALSE(
      ElabOk("virtual class VBase;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements VBase;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.2: the same prohibition applies when the implementing subject is itself
// a virtual class — a virtual class may implement interface classes but not a
// (non-interface) regular class.
TEST(ExtendsVsImplementsRestrictions, VirtualClassImplementsNonInterfaceError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "endclass\n"
             "virtual class VC implements Base;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassImplements, InheritedNonVirtualFromBaseDoesNotSatisfy) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "class BaseClass;\n"
             "  function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "class ExtClass extends BaseClass implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// A subclass that declares its own virtual method of the same name as a
// non-virtual base method hides that base method, and the override is what
// satisfies the implemented interface's pure virtual requirement.
TEST(InterfaceClassImplements,
     OwnVirtualOverrideHidesNonVirtualBaseAndSatisfies) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void f();\n"
             "endclass\n"
             "class BaseClass;\n"
             "  function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "class ExtClass extends BaseClass implements IC;\n"
             "  virtual function void f();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
