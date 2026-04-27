#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeSimulation, ExplicitStaticInAutoFuncBlockPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int get_id();\n"
      "    begin\n"
      "      static int next_id = 0;\n"
      "      next_id = next_id + 1;\n"
      "      return next_id;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ExplicitAutoInStaticFuncBlockFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int get_val();\n"
      "    begin\n"
      "      automatic int temp = 10;\n"
      "      temp = temp + 1;\n"
      "      return temp;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_val();\n"
      "    result = get_val();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 11u);
}

// §6.21: A declared for-loop variable is automatic by default and lives in a
// scope local to the loop. Assigning to a same-named variable inside the loop
// shall not perturb a homonymous variable in the enclosing scope.
TEST(ScopeAndLifetimeSimulation, ForLoopVarHasLocalScope) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 100;\n"
      "    for (int x = 0; x < 5; x = x + 1) begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 100u);
}

// §6.21: Locals of a static function retain their value between calls
// because static lifetime spans the whole simulation.
TEST(ScopeAndLifetimeSimulation, StaticFunctionVarsPersist) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

// §6.21: Locals of an automatic function are reinitialised on every
// call, so no value carries over across invocations.
TEST(ScopeAndLifetimeSimulation, AutomaticFunctionVarsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

// §6.21: When no lifetime keyword is given on a function, the default
// lifetime is static; this is observable as cross-call accumulation.
TEST(ScopeAndLifetimeSimulation, DefaultFunctionIsStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

// §6.21: A function inside a module declared automatic inherits that
// default lifetime, so its locals reinitialise per call even without
// an explicit automatic keyword on the function itself.
TEST(ScopeAndLifetimeSimulation, DefaultLifetimeInAutoModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

}  // namespace
