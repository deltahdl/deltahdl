// §8.26.6.1

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Req: A method name conflict shall be resolved with a single method prototype
// or implementation that simultaneously provides an implementation for all pure
// virtual methods of the same name of any implemented interface class.

TEST(InterfaceClassMethodConflict, SingleImplCalledViaObject) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
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
      "endmodule\n", "result"), 42u);
}

// Req: That method shall also be a valid virtual method override for any
// inherited method of the same name.

TEST(InterfaceClassMethodConflict, ExtendsAndImplementsCallsResolvedMethod) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
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
      "endmodule\n", "result"), 99u);
}

// Req: An interface class may inherit multiple methods with the same name; the
// implementing class resolves the conflict with a single method.

TEST(InterfaceClassMethodConflict, InterfaceExtendsConflictResolvesAtRuntime) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
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
      "endmodule\n", "result"), 7u);
}

}  // namespace
