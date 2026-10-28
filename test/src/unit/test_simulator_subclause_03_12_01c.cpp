#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §3.12.1 (printed page 56) searches for an identifier first in the scope
// that holds it, then in the part of the compilation-unit scope written before
// it, and only then up the instance hierarchy. A task's local b is its own:
// the task writes and reads it, 2, while the unit's b keeps 1, so
// `y * 10 + $unit::b` is 21. Resolved in the unit, both read 2: 22.
TEST(CompilationUnitSearchOrderSim, ASubroutineLocalIsFoundBeforeTheUnitsName) {
  EXPECT_EQ(RunAndGet("int b = 1;\n"
                      "module top;\n"
                      "  int y, r;\n"
                      "  task t;\n"
                      "    int b;\n"
                      "    b = 2;\n"
                      "    y = b;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    t();\n"
                      "    r = y * 10 + $unit::b;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            21u);
}

// The compilation-unit scope is searched before the instance hierarchy, so a
// child calling f, which neither it nor its own scope declares, runs the
// unit's f, 1, not the f of the module instantiating it, 2.
TEST(CompilationUnitSearchOrderSim,
     TheUnitsFunctionIsFoundBeforeAnEnclosingInstances) {
  EXPECT_EQ(RunAndGet("function int f();\n"
                      "  return 1;\n"
                      "endfunction\n"
                      "module child;\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  function int f();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "  child c();\n"
                      "endmodule\n",
                      "c.y"),
            1u);
}

// §3.12.1 (printed page 57): `$unit::` names the compilation-unit scope's own
// declaration past a nearer one of the name. The unit task's local b is 0 when
// `b = 5 + $unit::b;` runs, and $unit::b is the unit's 1, so the local becomes
// 6; read as the local, it became 5.
TEST(CompilationUnitSearchOrderSim,
     DollarUnitReachesTheUnitsVariablePastATaskLocal) {
  EXPECT_EQ(RunAndGet("bit b = 1;\n"
                      "int r;\n"
                      "task t;\n"
                      "  int b;\n"
                      "  b = 5 + $unit::b;\n"
                      "  r = b;\n"
                      "endtask\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    t();\n"
                      "    y = r;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            6u);
}

}  // namespace
