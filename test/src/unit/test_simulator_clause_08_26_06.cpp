// §8.26.6

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Req: When a class implements multiple interface classes, identifiers are
// merged from different name spaces into a single name space.

TEST(InterfaceClassNameMerging, MethodsFromMultipleInterfacesCallable) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
      "  pure virtual function int getA();\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function int getB();\n"
      "endclass\n"
      "class C implements IA, IB;\n"
      "  virtual function int getA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  virtual function int getB();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c_obj = new;\n"
      "    result = c_obj.getA() + c_obj.getB();\n"
      "  end\n"
      "endmodule\n", "result"), 3u);
}

// Req: When an interface class extends multiple interface classes, identifiers
// are merged from different name spaces into a single name space.

TEST(InterfaceClassNameMerging, ParamsFromMultipleExtendedInterfacesAccessible) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
      "  parameter int PA = 10;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int PB = 20;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = IC::PA + IC::PB;\n"
      "endmodule\n", "result"), 30u);
}

TEST(InterfaceClassNameMerging, TransitiveMergeMethodsCallable) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
      "  pure virtual function int getA();\n"
      "endclass\n"
      "interface class IB;\n"
      "  pure virtual function int getB();\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "  pure virtual function int getC();\n"
      "endclass\n"
      "class D implements IC;\n"
      "  virtual function int getA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  virtual function int getB();\n"
      "    return 2;\n"
      "  endfunction\n"
      "  virtual function int getC();\n"
      "    return 4;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    D d_obj = new;\n"
      "    result = d_obj.getA() + d_obj.getB() + d_obj.getC();\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

}  // namespace
