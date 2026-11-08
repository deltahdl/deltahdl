#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "has a method that is not pure virtual", 2,
                            "8.26"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassDataMemberError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain data members", 1, "8.26"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassStaticDataMemberError) {
  ElabFixture f;
  ElabOk(
      "interface class I;\n"
      "  static int n;\n"
      "endclass\n"
      "class A implements I;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain data members", 1, "8.26"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassConstDataMemberError) {
  ElabFixture f;
  ElabOk(
      "interface class I;\n"
      "  const int x = 1;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain data members", 1, "8.26"));
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
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
}

TEST(InterfaceClassImplements, MissingPureVirtualImplementation) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 4,
                            "8.26"));
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
  ElabFixture f;
  ElabOk(
      "interface class IA;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 7,
                            "8.26"));
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

TEST(InterfaceClassAllowedContent, NestedClassError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  class Nested;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain nested classes", 1, "8.26"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassNestedInInterfaceClassError) {
  ElabFixture f;
  ElabOk(
      "interface class Outer;\n"
      "  pure virtual function void foo();\n"
      "  interface class Inner;\n"
      "    pure virtual function void bar();\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain nested classes", 1, "8.26"));
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

TEST(InterfaceClassHandleAssign,
     NonImplementingClassNotAssignableToInterfaceHandle) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 12,
      "8.4"));
}

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

TEST(InterfaceClassInheritance, InterfaceClassExtendsRegularClassError) {
  ElabFixture f;
  ElabOk(
      "class SomeRegularClass;\n"
      "endclass\n"
      "interface class IC extends SomeRegularClass;\n"
      "  pure virtual function void f();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend non-interface class", 3, "8.26.2"));
}

TEST(InterfaceClassAllowedContent, InterfaceClassInsideAModuleDataMemberError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class IC;\n"
      "    int data;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain data members", 2, "8.26"));
}

TEST(InterfaceClassImplements,
     MissingPureVirtualImplementationInsideAModuleError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class IC;\n"
      "    pure virtual function void foo();\n"
      "  endclass\n"
      "  class C implements IC;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not implement pure virtual method", 5,
                            "8.26"));
}

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
