#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(InterfaceClassElaboration,
     EveryItemButPrototypesTypesAndParametersIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class I1;\n"
      "  int x;\n"
      "endclass\n"
      "interface class I2;\n"
      "  function void f(); endfunction\n"
      "endclass\n"
      "interface class I3;\n"
      "  virtual function void f(); endfunction\n"
      "endclass\n"
      "interface class I4;\n"
      "  constraint c { 1; }\n"
      "endclass\n"
      "interface class I5;\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "interface class I6;\n"
      "  class N; endclass\n"
      "endclass\n"
      "interface class I7;\n"
      "  interface class NI; endclass\n"
      "endclass\n"
      "interface class I8;\n"
      "  static function void f(); endfunction\n"
      "endclass\n"
      "interface class I9;\n"
      "  task t(); endtask\n"
      "endclass\n"
      "interface class I10;\n"
      "  rand int r;\n"
      "endclass\n"
      "interface class I11;\n"
      "  pure virtual function void f(); int y;\n"
      "endclass\n"
      "interface class OK;\n"
      "  typedef int t_t;\n"
      "  parameter int P = 1;\n"
      "  localparam int L = 2;\n"
      "  pure virtual function void f();\n"
      "  pure virtual task t();\n"
      "  ;\n"
      "  (* a *) pure virtual function int g(int a = 3);\n"
      "endclass : OK\n"
      "class Holder;\n"
      "  interface class HI; pure virtual function void f(); endclass\n"
      "endclass\n"
      "package pk;\n"
      "  interface class PI; pure virtual function void f(); endclass\n"
      "endpackage\n"
      "module m;\n"
      "  interface class MI; pure virtual function void f(); endclass\n"
      "endmodule\n"
      "interface ifc;\n"
      "  interface class FI; pure virtual function void f(); endclass\n"
      "endinterface\n"
      "program prg;\n"
      "  interface class GI; pure virtual function void f(); endclass\n"
      "endprogram\n"
      "interface class I12;\n"
      "  enum {A, B} e;\n"
      "endclass\n"
      "interface class I13 #(int Q = 1);\n"
      "  pure virtual function void f();\n"
      "endclass : I13\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {1, 28, 31, 58}) {
    EXPECT_TRUE(
        ReportedError(diags, "shall not contain data members", kLine, "8.26"))
        << kLine;
  }
  for (const int kLine : {5, 8, 23, 26}) {
    EXPECT_TRUE(ReportedError(diags, "has a method that is not pure virtual",
                              kLine, "8.26"))
        << kLine;
  }
  for (const int kLine : {10}) {
    EXPECT_TRUE(ReportedError(diags, "shall not contain constraint blocks",
                              kLine, "8.26.9"))
        << kLine;
  }
  for (const int kLine : {13}) {
    EXPECT_TRUE(
        ReportedError(diags, "shall not contain covergroups", kLine, "8.26.9"))
        << kLine;
  }
  for (const int kLine : {16, 19}) {
    EXPECT_TRUE(
        ReportedError(diags, "shall not contain nested classes", kLine, "8.26"))
        << kLine;
  }
  for (const int kLine : {34, 35, 36, 37, 39, 41, 44, 47, 50, 53, 56, 61}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(InterfaceClassElaboration,
     EveryPrototypeNeedsAVirtualImplementationAndADeclaredImplements) {
  ElabFixture f;
  ElaborateSrc(
      "interface class A; pure virtual function int fa(); endclass\n"
      "interface class B; typedef byte bt; parameter int P = 7; pure virtual "
      "function int fb(); endclass\n"
      "interface class AB extends A, B; pure virtual function bt fab(bt x = "
      "5); endclass\n"
      "class Base implements A; virtual function int fa(); return 1; "
      "endfunction endclass\n"
      "class Sub extends Base; endclass\n"
      "class Impl implements AB;\n"
      "  virtual function int fa(); return 2; endfunction\n"
      "  virtual function int fb(); return 3; endfunction\n"
      "  virtual function AB::bt fab(AB::bt x = AB::P); return x; endfunction\n"
      "endclass\n"
      "class Missing implements A; endclass\n"
      "class MissingOne implements AB;\n"
      "  virtual function int fa(); return 2; endfunction\n"
      "  virtual function int fb(); return 3; endfunction\n"
      "endclass\n"
      "class NoVirt implements A; function int fa(); return 4; endfunction "
      "endclass\n"
      "class Struct; virtual function int fa(); return 5; endfunction "
      "endclass\n"
      "virtual class VPart implements A; endclass\n"
      "class BaseV; virtual function int fa(); return 6; endfunction endclass\n"
      "class InhV extends BaseV implements A; endclass\n"
      "class BaseNV; function int fa(); return 7; endfunction endclass\n"
      "class InhNV extends BaseNV implements A; endclass\n"
      "class InhNVFix extends BaseNV implements A; virtual function int fa(); "
      "return 8; endfunction endclass\n"
      "module m;\n"
      "  A ah;\n"
      "  Sub s;\n"
      "  Struct st;\n"
      "  initial begin\n"
      "    s = new;\n"
      "    ah = s;\n"
      "    st = new;\n"
      "    ah = st;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {11, 12, 16, 22}) {
    EXPECT_TRUE(ReportedError(diags, "does not implement pure virtual method",
                              kLine, "8.26"))
        << kLine;
  }
  for (const int kLine : {18}) {
    EXPECT_TRUE(ReportedError(diags, "neither implements nor re-declares",
                              kLine, "8.26.7"))
        << kLine;
  }
  for (const int kLine : {32}) {
    EXPECT_TRUE(ReportedError(
        diags, "class handle assignment requires assignment compatible types",
        kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {4, 5, 6, 20, 23, 30}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
