// §8.26.6.2

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Req: The subclass shall provide parameter and/or type declarations that
// override all such name collisions. Verify the override value is accessible.

TEST(InterfaceClassParamTypeConflict, ResolvedParamAccessibleAtRuntime) {
  EXPECT_EQ(RunAndGet(
      "interface class IA;\n"
      "  parameter int P = 1;\n"
      "endclass\n"
      "interface class IB;\n"
      "  parameter int P = 2;\n"
      "endclass\n"
      "interface class IC extends IA, IB;\n"
      "  parameter int P = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = IC::P;\n"
      "endmodule\n", "result"), 42u);
}

TEST(InterfaceClassParamTypeConflict, LrmExampleResolvedTypeUsableAtRuntime) {
  EXPECT_EQ(RunAndGet(
      "interface class PutImp#(type T = logic);\n"
      "  pure virtual function void put(T a);\n"
      "endclass\n"
      "interface class GetImp#(type T = logic);\n"
      "  pure virtual function T get();\n"
      "endclass\n"
      "interface class PutGetIntf#(type TYPE = logic)\n"
      "    extends PutImp#(TYPE), GetImp#(TYPE);\n"
      "  typedef TYPE T;\n"
      "endclass\n"
      "class Fifo implements PutGetIntf#(int);\n"
      "  int store;\n"
      "  virtual function void put(int a);\n"
      "    store = a;\n"
      "  endfunction\n"
      "  virtual function int get();\n"
      "    return store;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Fifo f = new;\n"
      "    f.put(77);\n"
      "    result = f.get();\n"
      "  end\n"
      "endmodule\n", "result"), 77u);
}

}  // namespace
