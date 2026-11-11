#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodDefaults, MatchingDefaultValuesOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MultipleDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a = 0, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a = 0, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MixedDefaultAndNonDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ImplementorMissingDefaultError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo(int a = 5);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo(int a);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value presence does not match interface",
                            5, "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, ImplementorAddsUnexpectedDefaultError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo(int a);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo(int a = 5);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value presence does not match interface",
                            5, "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, MultipleImplementorsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int get(int a = 10);\n"
             "endclass\n"
             "class A implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, InheritedInterfaceDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class Base;\n"
             "  pure virtual function int foo(int a = 3);\n"
             "endclass\n"
             "interface class Derived extends Base;\n"
             "endclass\n"
             "class C implements Derived;\n"
             "  virtual function int foo(int a = 3);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MismatchedDefaultValueError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo(int a = 5);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo(int a = 10);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value does not match interface", 5,
                            "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, MismatchedSecondDefaultValueError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function int calc(int a = 0, int b = 1);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function int calc(int a = 0, int b = 99);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value does not match interface", 5,
                            "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, NonConstantDefaultValueError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo(int a = x);\n"
      "endclass\n"
      "module m;\n"
      "  int x = 5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value must be a constant expression", 2,
                            "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, ConstantExpressionDefaultValueOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 3 + 4);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 3 + 4);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, SecondImplementorMismatchedDefaultError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function int get(int a = 10);\n"
      "endclass\n"
      "class A implements IC;\n"
      "  virtual function int get(int a = 10);\n"
      "    return a;\n"
      "  endfunction\n"
      "endclass\n"
      "class B implements IC;\n"
      "  virtual function int get(int a = 20);\n"
      "    return a;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value does not match interface", 10,
                            "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, EquivalentConstantExpressionDefaultsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 2 + 3);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults,
     ConstantExpressionDefaultValueMismatchError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function int foo(int a = 5);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function int foo(int a = 2 + 2);\n"
      "    return a;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value does not match interface", 5,
                            "8.26.8"));
}

TEST(InterfaceClassMethodDefaults, LocalparamConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("localparam int K = 5;\n"
             "interface class IC;\n"
             "  pure virtual function int foo(int a = K);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = K);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ClassParameterConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC #(int P = 7);\n"
             "  pure virtual function int foo(int a = P);\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ParameterConstantDefaultOk) {
  EXPECT_TRUE(
      ElabOk("parameter int P = 8;\n"
             "interface class IC;\n"
             "  pure virtual function int foo(int a = P);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = P);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, LocalparamDefaultValueMismatchError) {
  ElabFixture f;
  ElabOk(
      "localparam int K = 5;\n"
      "interface class IC;\n"
      "  pure virtual function int foo(int a = K);\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function int foo(int a = 6);\n"
      "    return a;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value does not match interface", 6,
                            "8.26.8"));
}

TEST(InterfaceClassDefaultArgElaboration, NonConstantDefaultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "localparam int K = 4;\n"
      "interface class ID;\n"
      "  parameter int W = 10;\n"
      "  pure virtual function int f(int a = W + 1);\n"
      "  pure virtual function int g(int a = K);\n"
      "endclass\n"
      "class CD implements ID;\n"
      "  localparam int W = 50;\n"
      "  virtual function int f(int a = ID::W + 1); return a; endfunction\n"
      "  virtual function int g(int a = 4); return a; endfunction\n"
      "endclass\n"
      "class CD2 implements ID;\n"
      "  virtual function int f(int a = 11); return a * 2; endfunction\n"
      "  virtual function int g(int a = K); return a * 2; endfunction\n"
      "endclass\n"
      "int gv = 3;\n"
      "interface class IBad;\n"
      "  pure virtual function int h(int a = gv);\n"
      "endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  ID ih;\n"
      "  initial begin\n"
      "    CD c; CD2 c2;\n"
      "    c = new; c2 = new;\n"
      "    ih = c;\n"
      "    r1 = ih.f();\n"
      "    r2 = ih.g();\n"
      "    ih = c2;\n"
      "    r3 = ih.f();\n"
      "    r4 = ih.g();\n"
      "    r5 = c.f();\n"
      "    r6 = c2.f(7);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {18}) {
    EXPECT_TRUE(ReportedError(
        diags, "default value must be a constant expression", kLine, "8.26.8"))
        << kLine;
  }
  for (const int kLine : {4, 5, 9, 10, 13, 14}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
