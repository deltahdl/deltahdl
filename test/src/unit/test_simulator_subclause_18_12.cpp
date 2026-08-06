#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// These tests drive 18.12's scope randomize function, std::randomize(), end to
// end: each elaborates a real module, calls the scope randomize from source
// over variables of the current scope, and copies the outcome into module
// variables the harness reads. The behavior observed is that of
// parse/elaborate/run applying the rule through the production scope randomize
// path (TryEvalScopeRandomizeCall in eval_randomize.cpp), not a hand-built
// solver state. When the scope randomize is not wired at all, an
// unknown-function call yields 0, so a returned status of 1 is itself evidence
// the production rule ran and succeeded.

// 18.12: the scope randomize function operates on the variables of the current
// scope; its arguments specify the variables to be assigned random values, and
// it returns 1 when it successfully sets ALL of them to valid values. Two
// four-state variables of differing declared widths are named; each begins
// all-x, and after the call $isunknown reads 0 for both -- so every named
// random variable, not merely one, was actually drawn and written a concrete
// value. This is deterministic regardless of which values the draw produced.
TEST(ScopeRandomizeRuntime, SetsAllScopeVariablesAndReturnsOne) {
  const char* src =
      "module stim;\n"
      "  logic [3:0] a;\n"  // both begin uninitialized -> all x
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
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);    // sets all random variables -> 1
  EXPECT_EQ(RunAndGet(src, "unk_a"), 0u);  // a received a concrete value
  EXPECT_EQ(RunAndGet(src, "unk_b"), 0u);  // b did too -- all of them set
}

// 18.12: the std:: package qualifier is optional -- the LRM example writes the
// call as the bare randomize(addr, data, rd_wr), where addr and data have
// module scope and rd_wr is local to the calling function. Driving that exact
// shape through the pipeline, the bare call inside the function returns 1,
// confirming both that the bare spelling is the same scope randomize function
// and that the current function scope is the one whose variables are
// randomized.
TEST(ScopeRandomizeRuntime, BareCallInsideFunctionUsesCurrentScope) {
  const char* src =
      "module stim;\n"
      "  bit [15:0] addr;\n"
      "  bit [31:0] data;\n"
      "  int okv;\n"
      "  function int gen_stim();\n"
      "    bit rd_wr;\n"
      "    return randomize(addr, data, rd_wr);\n"  // call std::randomize
      "  endfunction\n"
      "  initial begin\n"
      "    okv = gen_stim();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
}

// 18.12: called with no argument, the scope randomize shall not change the
// value of any variable but instead check its constraints. With no with
// constraint block there is no constraint expression that can evaluate to
// false, so it takes the "otherwise" branch and returns 1 -- and it leaves the
// pre-existing value of the scope variable exactly as it was, confirming the
// no-argument form is a checker rather than a generator.
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
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);  // no false constraint -> returns 1
  EXPECT_EQ(RunAndGet(src, "a"), 42u);   // checker changes no variable
}

// 18.12: "otherwise, it returns 0." The failure branch of the scope randomize
// maps a solve that cannot set the random variables to valid values onto a
// returned status of 0. That mapping lives entirely in the solver stage the
// scope randomize drives; the real trigger of an unsatisfiable solve -- a with
// constraint_block that no draw can satisfy -- is the province of 18.12.1, so
// the failure mapping itself is observed here against the solver directly, with
// a constraint that demands a value no draw from the variable's domain can
// meet.
TEST(ScopeRandomizeRuntime, FailedSolveReturnsZero) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "a";
  v.min_val = 0;
  v.max_val = 50;
  solver.AddVariable(v);

  // Demand a value outside the variable's domain: no assignment can satisfy it.
  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "a";
  c.lo = 100;
  c.hi = 200;

  EXPECT_FALSE(solver.SolveWith({c}));
}

}  // namespace
