// §8.26.2

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

}  // namespace
