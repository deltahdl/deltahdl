

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodConflict, SingleImplCalledViaObject) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "class C implements IA, IB;\n"
                      "  virtual function int f();\n"
                      "    return 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj = new;\n"
                      "    result = obj.f();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(InterfaceClassMethodConflict, ExtendsAndImplementsCallsResolvedMethod) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "virtual class Base;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "class C extends Base implements IA, IB;\n"
                      "  virtual function int f();\n"
                      "    return 99;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C obj = new;\n"
                      "    result = obj.f();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(InterfaceClassMethodConflict, InterfaceExtendsConflictResolvesAtRuntime) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IC extends IA, IB;\n"
                      "endclass\n"
                      "class D implements IC;\n"
                      "  virtual function int f();\n"
                      "    return 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D obj = new;\n"
                      "    result = obj.f();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

}  // namespace
