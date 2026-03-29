#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassPartialImplementationSim,
     ConcreteCompletesPartialAndCallsMethod) {
  EXPECT_EQ(RunAndGet(
      "interface class IntfClass;\n"
      "  pure virtual function int funcA();\n"
      "  pure virtual function int funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "  virtual function int funcA();\n"
      "    return 10;\n"
      "  endfunction\n"
      "  pure virtual function int funcB();\n"
      "endclass\n"
      "class ClassB extends ClassA;\n"
      "  virtual function int funcB();\n"
      "    return 20;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    ClassB obj;\n"
      "    obj = new;\n"
      "    result = obj.funcA() + obj.funcB();\n"
      "  end\n"
      "endmodule\n", "result"), 30u);
}

TEST(InterfaceClassPartialImplementationSim,
     ConcreteCalledViaInterfaceHandle) {
  EXPECT_EQ(RunAndGet(
      "interface class IntfClass;\n"
      "  pure virtual function int funcA();\n"
      "  pure virtual function int funcB();\n"
      "endclass\n"
      "virtual class ClassA implements IntfClass;\n"
      "  virtual function int funcA();\n"
      "    return 10;\n"
      "  endfunction\n"
      "  pure virtual function int funcB();\n"
      "endclass\n"
      "class ClassB extends ClassA;\n"
      "  virtual function int funcB();\n"
      "    return 20;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    ClassB obj;\n"
      "    IntfClass iref;\n"
      "    obj = new;\n"
      "    iref = obj;\n"
      "    result = iref.funcA() + iref.funcB();\n"
      "  end\n"
      "endmodule\n", "result"), 30u);
}

TEST(InterfaceClassPartialImplementationSim,
     ChainedVirtualClassesCompletedByConcrete) {
  EXPECT_EQ(RunAndGet(
      "interface class IntfClass;\n"
      "  pure virtual function int funcA();\n"
      "  pure virtual function int funcB();\n"
      "  pure virtual function int funcC();\n"
      "endclass\n"
      "virtual class V1 implements IntfClass;\n"
      "  virtual function int funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  pure virtual function int funcB();\n"
      "  pure virtual function int funcC();\n"
      "endclass\n"
      "virtual class V2 extends V1;\n"
      "  virtual function int funcB();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endclass\n"
      "class Concrete extends V2;\n"
      "  virtual function int funcC();\n"
      "    return 4;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Concrete obj;\n"
      "    obj = new;\n"
      "    result = obj.funcA() + obj.funcB() + obj.funcC();\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

}  // namespace
