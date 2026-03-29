#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassTypeUsageRestrictions, InterfaceDeclaredBeforeUseOk) {
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

TEST(InterfaceClassTypeUsageRestrictions, ParameterizedInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC #(type T = int);\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req 1: A class shall not implement a type parameter.

TEST(InterfaceClassTypeUsageRestrictions, ClassImplementsTypeParamError) {
  EXPECT_FALSE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo #(type T = PutImp) implements T;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, VirtualClassImplementsTypeParamError) {
  EXPECT_FALSE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "virtual class Fifo #(type T = PutImp) implements T;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsConcreteAndTypeParamError) {
  EXPECT_FALSE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "class C #(type T = B) implements A, T;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req 2: An interface class shall not extend a type parameter.

TEST(InterfaceClassTypeUsageRestrictions, InterfaceExtendsTypeParamError) {
  EXPECT_FALSE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "interface class Fifo #(type T = PutImp) extends T;\n"
             "  pure virtual function void get();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsConcreteAndTypeParamError) {
  EXPECT_FALSE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class C #(type T = B) extends A, T;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req 3: A class shall not implement a forward typedef for an interface class.

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsForwardTypedefError) {
  EXPECT_FALSE(
      ElabOk("typedef interface class IC;\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     VirtualClassImplementsForwardTypedefError) {
  EXPECT_FALSE(
      ElabOk("typedef interface class IC;\n"
             "virtual class VC implements IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req 4: An interface class shall not extend from a forward typedef of an
// interface class.

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsForwardTypedefError) {
  EXPECT_FALSE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC2 extends IC;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req 5: An interface class shall be declared before it is implemented or
// extended.

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsUndeclaredInterfaceError) {
  EXPECT_FALSE(
      ElabOk("class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsUndeclaredInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface class IC2 extends IC;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Positive: using a type parameter as an argument to a concrete interface
// (not as the implemented/extended type itself) is legal.

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsInterfaceWithTypeParamArgOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp #(type T = logic);\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo #(type T = int) implements PutImp #(T);\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsInterfaceWithTypeParamArgOk) {
  EXPECT_TRUE(
      ElabOk("interface class A #(type T = logic);\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B #(type T = bit) extends A #(T);\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Positive: forward typedef followed by full declaration, then implements
// (declaration before use) is legal.

TEST(InterfaceClassTypeUsageRestrictions,
     ForwardTypedefThenDeclThenImplementsOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ForwardTypedefThenDeclThenExtendsOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "interface class IC2 extends IC;\n"
             "  pure virtual function void bar();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
