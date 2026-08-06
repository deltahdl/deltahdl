

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

// Claim A (runtime): the conflict is resolved by a single pure virtual
// prototype re-declared in an intervening abstract virtual class, with the
// concrete implementation supplied by the derived class. Dispatching through
// the derived handle must reach that derived implementation.
TEST(InterfaceClassMethodConflict, VirtualClassPrototypeResolvedMethodCalled) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "virtual class V implements IA, IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "class C extends V;\n"
                      "  virtual function int f();\n"
                      "    return 55;\n"
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
            55u);
}

// Claim A (runtime): the single resolving method is not declared in the
// implementing class at all but inherited as a concrete method from a base
// class; that inherited method must be the one dispatched when the derived
// object's method is called.
TEST(InterfaceClassMethodConflict, InheritedConcreteMethodResolvesAtRuntime) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function int f();\n"
                      "endclass\n"
                      "class Base;\n"
                      "  virtual function int f();\n"
                      "    return 88;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base implements IA, IB;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived obj = new;\n"
                      "    result = obj.f();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            88u);
}

}  // namespace
