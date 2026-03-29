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

TEST(InterfaceClasses, ClassExtendsInterfaceClassError) {
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

TEST(InterfaceClassImplements, ImplementingClassScopeResOk) {
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

}  // namespace
