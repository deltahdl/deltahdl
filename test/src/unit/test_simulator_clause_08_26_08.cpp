#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodDefaultsSim, CallWithDefaultArgValue) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
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
      "endmodule\n", "result"), 42u);
}

TEST(InterfaceClassMethodDefaultsSim, CallWithExplicitArgOverridesDefault) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
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
      "endmodule\n", "result"), 7u);
}

TEST(InterfaceClassMethodDefaultsSim, CallViaInterfaceHandleUsesDefault) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
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
      "endmodule\n", "result"), 99u);
}

TEST(InterfaceClassMethodDefaultsSim, MultipleDefaultArgsSomeOmitted) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
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
      "endmodule\n", "result"), 15u);
}

TEST(InterfaceClassMethodDefaultsSim, DefaultArgConstantExpression) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
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
      "endmodule\n", "result"), 13u);
}

TEST(InterfaceClassMethodDefaultsSim, InheritedDefaultArgViaExtends) {
  EXPECT_EQ(RunAndGet(
      "interface class Base;\n"
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
      "endmodule\n", "result"), 25u);
}

}  // namespace
