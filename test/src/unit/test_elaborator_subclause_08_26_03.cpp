#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassTypeAccess, TypedefInheritedByExtendingInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA;\n"
             "  typedef int my_t;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfA;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ParamInheritedByExtendingInterface) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA;\n"
             "  parameter int SIZE = 64;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfA;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, TypedefUsedInExtendingInterfaceMethod) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA #(type T1 = logic);\n"
             "  typedef T1[1:0] T2;\n"
             "  pure virtual function T2 funcA();\n"
             "endclass\n"
             "interface class IntfB #(type T = bit) extends IntfA #(T);\n"
             "  pure virtual function T2 funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ChainedTypedefInheritanceThroughExtends) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  typedef int my_t;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB extends IA;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class IC extends IB;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToTypedef) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IntfC::t1_t x;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToParam) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  parameter int WIDTH = 8;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IC::WIDTH;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, ScopeResolutionAccessToEnumValue) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = IntfC::ONE;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess,
     ScopeResolutionAccessToTypedefOfSpecializedInterfaceClass) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA #(type T1 = logic);\n"
             "  typedef T1[1:0] T2;\n"
             "  pure virtual function T2 funcA();\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    IntfA#(bit)::T2 val;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInImplementingClassIsError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfC;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function t1_t funcC();\n"
      "endclass\n"
      "class ClassA implements IntfC;\n"
      "  t1_t t1_i;\n"
      "  virtual function IntfC::t1_t funcC();\n"
      "    return (IntfC::ONE);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not inherited from interface class", 6,
                            "8.26.3"));
}

TEST(InterfaceClassTypeAccess, TypedefQualifiedMemberInImplementingClassOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  IntfC::t1_t t1_i;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess,
     PlainTypedefUnqualifiedInImplementingClassIsError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfC;\n"
      "  typedef int my_t;\n"
      "  pure virtual function my_t funcC();\n"
      "endclass\n"
      "class ClassA implements IntfC;\n"
      "  my_t m_i;\n"
      "  virtual function IntfC::my_t funcC();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not inherited from interface class", 6,
                            "8.26.3"));
}

TEST(InterfaceClassTypeAccess, LocalTypedefShadowsInterfaceTypedef) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef enum {ONE, TWO, THREE} t1_t;\n"
             "  pure virtual function t1_t funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  typedef int t1_t;\n"
             "  t1_t t1_i;\n"
             "  virtual function IntfC::t1_t funcC();\n"
             "    return (IntfC::ONE);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInMethodArgumentIsError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfC;\n"
      "  typedef int int_t;\n"
      "  pure virtual function void hello(int_t val);\n"
      "endclass\n"
      "class Hello implements IntfC;\n"
      "  virtual function void hello(int_t val);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not inherited from interface class", 6,
                            "8.26.3"));
}

TEST(InterfaceClassTypeAccess, TypedefUnqualifiedInMethodReturnTypeIsError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfC;\n"
      "  typedef int int_t;\n"
      "  pure virtual function int_t hello();\n"
      "endclass\n"
      "class Hello implements IntfC;\n"
      "  virtual function int_t hello();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not inherited from interface class", 6,
                            "8.26.3"));
}

TEST(InterfaceClassTypeAccess, TypedefQualifiedInMethodSignatureOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function int_t hello(int_t val);\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  virtual function IntfC::int_t hello(IntfC::int_t val);\n"
             "    return val;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccess,
     TypedefUnqualifiedInMethodArgumentInsideAModuleIsError) {
  ElabFixture f;
  ElabOk(
      "module class_tb;\n"
      "  interface class ihello;\n"
      "    typedef int int_t;\n"
      "    pure virtual function void hello(int_t val);\n"
      "  endclass\n"
      "  class Hello implements ihello;\n"
      "    virtual function void hello(int_t val);\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not inherited from interface class", 7,
                            "8.26.3"));
}

TEST(InterfaceClassTypeAccess, LocalTypedefShadowsInterfaceTypedefInArgument) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  typedef int int_t;\n"
             "  pure virtual function void hello(int_t val);\n"
             "endclass\n"
             "class Hello implements IntfC;\n"
             "  typedef int int_t;\n"
             "  virtual function void hello(int_t val);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassTypeAccessElaboration,
     DISABLED_ImplementingClassNamesNoInterfaceMemberUnqualified) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IntfC;\n"
      "  parameter int SIZE = 64;\n"
      "  localparam int LP = 3;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function t1_t funcC();\n"
      "endclass\n"
      "class ClassA implements IntfC;\n"
      "  int x = SIZE;\n"
      "  bit [SIZE-1:0] v;\n"
      "  virtual function IntfC::t1_t funcC();\n"
      "    t1_t local_v;\n"
      "    int y;\n"
      "    y = LP;\n"
      "    y = $bits(t1_t);\n"
      "    y = t1_t'(1);\n"
      "    return ONE;\n"
      "  endfunction\n"
      "  function int h(int a = SIZE); return a; endfunction\n"
      "endclass\n"
      "class D extends ClassA;\n"
      "  int z = SIZE;\n"
      "endclass\n"
      "class ClassOk implements IntfC;\n"
      "  int x = IntfC::SIZE;\n"
      "  localparam int SIZE = 5;\n"
      "  int w = SIZE;\n"
      "  virtual function IntfC::t1_t funcC();\n"
      "    IntfC::t1_t local_v;\n"
      "    int y;\n"
      "    y = IntfC::LP;\n"
      "    return IntfC::ONE;\n"
      "  endfunction\n"
      "endclass\n"
      "interface class IX extends IntfC;\n"
      "  pure virtual function t1_t fx(int a = SIZE + LP);\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    ClassOk o; o = new;\n"
      "    r1 = o.x; r2 = o.w; r3 = o.funcC();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "SIZE", 8, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 9, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 11, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "LP", 13, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 14, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 15, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "ONE", 16, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 18, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 21, "8.26.3"));
  EXPECT_FALSE(ErrorOnLine(diags, 23));
}

TEST(
    InterfaceClassTypeAccessElaboration,
    DISABLED_ModuleOrPackageImplementingClassNamesNoInterfaceMemberUnqualified) {
  ElabFixture f;
  ElaborateSrc(
      "module mm;\n"
      "  interface class IntfC;\n"
      "    parameter int SIZE = 64;\n"
      "    localparam int LP = 3;\n"
      "    typedef enum {ONE, TWO, THREE} t1_t;\n"
      "    pure virtual function t1_t funcC();\n"
      "  endclass\n"
      "  class ClassA implements IntfC;\n"
      "    int x = SIZE;\n"
      "    bit [SIZE-1:0] v;\n"
      "    virtual function IntfC::t1_t funcC();\n"
      "      t1_t local_v;\n"
      "      int y;\n"
      "      y = LP;\n"
      "      y = $bits(t1_t);\n"
      "      y = t1_t'(1);\n"
      "      return ONE;\n"
      "    endfunction\n"
      "    function int h(int a = SIZE); return a; endfunction\n"
      "  endclass\n"
      "  class D extends ClassA;\n"
      "    int z = SIZE;\n"
      "  endclass\n"
      "endmodule\n"
      "package pp;\n"
      "  interface class IntfC;\n"
      "    parameter int SIZE = 64;\n"
      "    localparam int LP = 3;\n"
      "    typedef enum {ONE, TWO, THREE} t1_t;\n"
      "    pure virtual function t1_t funcC();\n"
      "  endclass\n"
      "  class ClassA implements IntfC;\n"
      "    int x = SIZE;\n"
      "    bit [SIZE-1:0] v;\n"
      "    virtual function IntfC::t1_t funcC();\n"
      "      t1_t local_v;\n"
      "      int y;\n"
      "      y = LP;\n"
      "      y = $bits(t1_t);\n"
      "      y = t1_t'(1);\n"
      "      return ONE;\n"
      "    endfunction\n"
      "    function int h(int a = SIZE); return a; endfunction\n"
      "  endclass\n"
      "  class D extends ClassA;\n"
      "    int z = SIZE;\n"
      "  endclass\n"
      "endpackage\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "SIZE", 9, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 10, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 12, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "LP", 14, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 15, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 16, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "ONE", 17, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 19, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 22, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 33, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 34, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 36, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "LP", 38, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 39, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "t1_t", 40, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "ONE", 41, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 43, "8.26.3"));
  EXPECT_TRUE(ReportedError(diags, "SIZE", 46, "8.26.3"));
}

}  // namespace
