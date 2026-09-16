#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(CompilationUnitSim, CuScopeFunctionCallableFromModule) {
  auto val = RunAndGet(
      "function int helper(int x); return x + 1; endfunction\n"
      "module top;\n"
      "  int observed;\n"
      "  initial observed = helper(5);\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 6u);
}

TEST(CompilationUnitSim, MultipleCuScopeFunctionsResolvedAtRuntime) {
  auto val = RunAndGet(
      "function int twice(int x); return x * 2; endfunction\n"
      "function int add_one(int x); return x + 1; endfunction\n"
      "module top;\n"
      "  int observed;\n"
      "  initial observed = twice(add_one(3));\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 8u);
}

// §3.12.1 and §6.19: an enumeration a typedef declares at compilation-unit
// scope declares its literals for the modules of the unit, so a module reads
// MID as 1 and a class method of the unit compares against JUMBO.
TEST(CompilationUnitSim, CuScopeEnumLiteralsResolveInModulesAndClasses) {
  auto val = RunAndGet(
      "typedef enum {LOW, MID, HIGH} level_t;\n"
      "class Reader;\n"
      "  function int is_high(level_t l);\n"
      "    return l == HIGH;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    Reader o = new;\n"
      "    r = MID + 10 * o.is_high(HIGH);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 11u);
}

}  // namespace
