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

}  // namespace
