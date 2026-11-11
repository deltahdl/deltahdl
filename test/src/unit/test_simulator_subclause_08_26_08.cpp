#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodDefaultsSim, CallWithDefaultArgValue) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function int foo(int a = 42);\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function int foo(int a = 42);\n"
                      "    return a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    obj = new;\n"
                      "    result = obj.foo();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(InterfaceClassMethodDefaultsSim, CallWithExplicitArgOverridesDefault) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function int foo(int a = 42);\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function int foo(int a = 42);\n"
                      "    return a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    obj = new;\n"
                      "    result = obj.foo(7);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(InterfaceClassMethodDefaultsSim, CallViaInterfaceHandleUsesDefault) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function int foo(int a = 99);\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function int foo(int a = 99);\n"
                      "    return a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    IC iref;\n"
                      "    obj = new;\n"
                      "    iref = obj;\n"
                      "    result = iref.foo();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(InterfaceClassMethodDefaultsSim, MultipleDefaultArgsSomeOmitted) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function int calc(int a, int b = 10);\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function int calc(int a, int b = 10);\n"
                      "    return a + b;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    obj = new;\n"
                      "    result = obj.calc(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(InterfaceClassMethodDefaultsSim, DefaultArgConstantExpression) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function int foo(int a = 3 * 4 + 1);\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function int foo(int a = 3 * 4 + 1);\n"
                      "    return a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    obj = new;\n"
                      "    result = obj.foo();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            13u);
}

TEST(InterfaceClassMethodDefaultsSim, InheritedDefaultArgViaExtends) {
  EXPECT_EQ(RunAndGet("interface class Base;\n"
                      "  pure virtual function int foo(int a = 25);\n"
                      "endclass\n"
                      "interface class Derived extends Base;\n"
                      "endclass\n"
                      "class C implements Derived;\n"
                      "  virtual function int foo(int a = 25);\n"
                      "    return a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj;\n"
                      "    obj = new;\n"
                      "    result = obj.foo();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            25u);
}

TEST(InterfaceClassDefaultArgSim, DefaultIsEvaluatedWhereTheMethodIsDeclared) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
  LowerRunAndCheck(f, design,
                   {{"r1", 11u},
                    {"r2", 4u},
                    {"r3", 22u},
                    {"r4", 8u},
                    {"r5", 11u},
                    {"r6", 14u}});
}

TEST(InterfaceClassDefaultArgSim,
     DISABLED_DefaultNamingAnInheritedParameterIsConstant) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class B; parameter int P = 7; localparam int L = 2; pure "
      "virtual function int fb(); endclass\n"
      "interface class AB extends B; pure virtual function int fab(int x = P + "
      "L); endclass\n"
      "class Impl implements AB;\n"
      "  virtual function int fb(); return 0; endfunction\n"
      "  virtual function int fab(int x = AB::P + AB::L); return x; "
      "endfunction\n"
      "endclass\n"
      "module m;\n"
      "  AB h;\n"
      "  Impl i;\n"
      "  int r1;\n"
      "  initial begin\n"
      "    i = new;\n"
      "    h = i;\n"
      "    r1 = h.fab();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 9u}});
}

}  // namespace
