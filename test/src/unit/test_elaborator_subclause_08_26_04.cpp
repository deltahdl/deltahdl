#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(InterfaceClassTypeUsageRestrictions, ClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "class Fifo #(type T = PutImp) implements T;\n"
      "  virtual function void put();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            4, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     VirtualClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "virtual class Fifo #(type T = PutImp) implements T;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            4, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsConcreteAndTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            7, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions, InterfaceExtendsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "interface class Fifo #(type T = PutImp) extends T;\n"
      "  pure virtual function void get();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be extended", 4,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsConcreteAndTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "interface class C #(type T = B) extends A, T;\n"
      "  pure virtual function void fc();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be extended", 7,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  typedef interface class IC;\n"
      "  class C implements IC;\n"
      "    virtual function void foo();\n"
      "    endfunction\n"
      "  endclass\n"
      "  interface class IC;\n"
      "    pure virtual function void foo();\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "but the interface class's full declaration has to "
                            "precede every class that implements it",
                            3, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAModuleImplementsInterfaceDeclaredAheadOfItOk) {
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

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAPackageImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAnInterfaceImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface intf;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassInsideAProgramImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "program prog;\n"
      "  interface class PutImp;\n"
      "    pure virtual function void put();\n"
      "  endclass\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endprogram\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassNestedInAClassImplementsTypeParamError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "class Outer;\n"
      "  class Fifo #(type T = PutImp) implements T;\n"
      "    virtual function void put();\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "where only an interface class can be implemented",
                            5, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassNestedInAClassImplementsNamedInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Outer;\n"
             "  class Fifo implements PutImp;\n"
             "    virtual function void put();\n"
             "    endfunction\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeUsageRestrictions, ClassImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "but the interface class's full declaration has to "
                            "precede every class that implements it",
                            2, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsParameterizedForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IntfD;\n"
      "class ClassB implements IntfD #(bit);\n"
      "  virtual function void funcD();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IntfD #(type T1 = logic);\n"
      "  pure virtual function void funcD();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "but the interface class's full declaration has to "
                            "precede every class that implements it",
                            2, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     VirtualClassImplementsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "virtual class VC implements IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "but the interface class's full declaration has to "
                            "precede every class that implements it",
                            2, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions, InterfaceExtendsForwardTypedefError) {
  ElabFixture f;
  ElabOk(
      "typedef interface class IC;\n"
      "interface class IC2 extends IC;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "but the interface class's full declaration has to precede every "
      "interface class that extends it",
      2, "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     ClassImplementsUndeclaredInterfaceError) {
  ElabFixture f;
  ElabOk(
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "', which implements it", 1,
                            "8.26.4"));
}

TEST(InterfaceClassTypeUsageRestrictions,
     InterfaceExtendsUndeclaredInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class IC2 extends IC;\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "', which extends it", 1, "8.26.4"));
}

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

TEST(InterfaceClassTypeUsageRestrictions, ForwardTypedefThenDeclThenExtendsOk) {
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
