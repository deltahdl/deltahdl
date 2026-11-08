#include <gtest/gtest.h>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

TEST(ScopeRandomizeRuntime, SetsAllScopeVariablesAndReturnsOne) {
  const char* src =
      "module stim;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  int okv;\n"
      "  int unk_a;\n"
      "  int unk_b;\n"
      "  initial begin\n"
      "    okv = std::randomize(a, b);\n"
      "    unk_a = $isunknown(a);\n"
      "    unk_b = $isunknown(b);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "unk_a"), 0u);
  EXPECT_EQ(RunAndGet(src, "unk_b"), 0u);
}

TEST(ScopeRandomizeRuntime, BareCallInsideFunctionUsesCurrentScope) {
  const char* src =
      "module stim;\n"
      "  bit [15:0] addr;\n"
      "  bit [31:0] data;\n"
      "  int okv;\n"
      "  function int gen_stim();\n"
      "    bit rd_wr;\n"
      "    return randomize(addr, data, rd_wr);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    okv = gen_stim();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
}

TEST(ScopeRandomizeRuntime, NoArgumentCheckerReturnsOneAndChangesNothing) {
  const char* src =
      "module stim;\n"
      "  bit [7:0] a;\n"
      "  int okv;\n"
      "  initial begin\n"
      "    a = 8'd42;\n"
      "    okv = std::randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "a"), 42u);
}

TEST(ScopeRandomizeRuntime, FailedSolveReturnsZero) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "a";
  v.min_val = 0;
  v.max_val = 50;
  solver.AddVariable(v);

  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "a";
  c.lo = 100;
  c.hi = 200;

  EXPECT_FALSE(solver.SolveWith({c}));
}

}  // namespace
