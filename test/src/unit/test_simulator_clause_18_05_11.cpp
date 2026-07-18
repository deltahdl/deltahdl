#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive "functions in constraints" (18.5.11) end to end. Each
// program declares a class with rand variables (18.4.1) and a constraint that
// calls a function, calls randomize() from an initial block, and copies the
// outcome into module variables the harness reads. The parser records the
// unqualified call, the elaborator applies the argument restrictions, and the
// simulator lowers each random variable used as a function argument into the
// solver's implicit priority ordering (eval_randomize.cpp). The behavior
// observed here is therefore that of real elaborated source driven through the
// production randomize() path, not a hand-built solver state. The functions
// take input arguments only, as the clause requires.

// 18.5.11: a function called in a constraint is evaluated with its argument
// already committed, and its return value is used as a state variable by the
// consuming constraint. With y pinned to 3 and x constrained to equal dbl(y),
// randomize() must produce x == 6 every time — the function is called (once its
// argument is known) and its result drives the solve.
TEST(FunctionsInConstraints, FunctionResultUsedAsStateVariable) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int dbl(int a); return 2 * a; endfunction\n"
      "  constraint cy { y == 3; }\n"
      "  constraint cx { x == dbl(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 6u);
}

// 18.5.11: a random variable used as a function argument is solved ahead of the
// variable of the constraint that consumes it, so the argument is chosen from
// its own (here unconstrained) domain first and the consumer is fitted around
// it. In 'x <= 2*f(y)' the argument y is solved first, so it comes out uniform
// over 0..3 — each value about a quarter of the time. Without the implicit
// ordering a joint draw would weight larger y (which admit more legal x) far
// more heavily, making y == 0 rare (about 1/16); the near-quarter frequency is
// the signature of the argument-first ordering carried from source.
TEST(FunctionsInConstraints, ArgumentSolvedFirstGivesUniformArgument) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint c { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int y0;\n"
      "  int bad;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    y0 = 0;\n"
      "    bad = 0;\n"
      "    for (int i = 0; i < 800; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.y == 0) y0 = y0 + 1;\n"
      "      if (o.x > 2 * o.y) bad = bad + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ~200 (1/4 of 800). A wide band keeps the statistical test stable
  // while still excluding the joint-draw behavior (~50), which the ordering
  // moves away from.
  auto y0 = RunAndGet(src, "y0");
  EXPECT_GE(y0, 140u);
  EXPECT_LE(y0, 260u);
  // The consuming constraint must hold on every solve.
  EXPECT_EQ(RunAndGet(src, "bad"), 0u);
}

// 18.5.11: more than one argument may share the highest priority. When a
// constraint uses two variables as function arguments, both are solved before
// the consumer and enter the function call as state variables. With y and z
// pinned, x == f(y) + f(z) is forced to their sum, so x is 5.
TEST(FunctionsInConstraints, MultipleArgumentsSolvedBeforeConsumer) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [3:0] z;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cy { y == 2; }\n"
      "  constraint cz { z == 3; }\n"
      "  constraint cx { x == f(y) + f(z); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 5u);
}

// 18.5.11: a circular dependency created by the implicit variable ordering
// shall result in an error. Here each constraint uses the other's variable as a
// function argument — a is an argument to the constraint on b and b is an
// argument to the constraint on a — so each is required to be solved before the
// other. randomize() fails outright rather than solving a self-contradictory
// ordering.
TEST(FunctionsInConstraints, CircularArgumentOrderingFailsRandomize) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  function int id(int v); return v; endfunction\n"
      "  constraint c { a < id(b); b < id(a); }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.11: with no function call in a constraint no implicit ordering is
// recorded, so the solver keeps its ordinary flat behavior and the constraint
// solves directly. This confirms the argument-priority lowering is inert unless
// a function argument actually appears — an ordinary constraint is unaffected.
TEST(FunctionsInConstraints, NoFunctionCallLeavesFlatSolveUnchanged) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] y;\n"
      "  constraint c { x == y; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int eq;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    eq = (o.x == o.y);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
}

// 18.5.11: within a prioritized set the cyclical (randc) variables are solved
// first. A randc variable keeps its no-repeat cyclic behavior even while a
// function-argument priority orders the rand variables of the same solve: the
// constraint x <= 2*f(y) makes y outrank x, engaging the priority-layer pass,
// yet the randc c is committed ahead of that pass and so still visits each of
// its four values exactly once across one full iteration. Accumulating the four
// draws into a bitmask leaves every bit set (4'b1111 == 15) only if no value
// repeated within the iteration.
TEST(FunctionsInConstraints, RandcCyclesWhileArgumentPriorityActive) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] c;\n"
      "  rand bit [1:0] y;\n"
      "  rand bit [3:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cx { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int seen;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    seen = 0;\n"
      "    for (int i = 0; i < 4; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      seen = seen | (1 << o.c);\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // One complete randc iteration over a 2-bit variable visits 0,1,2,3 once
  // each, so every bit of the mask is set.
  EXPECT_EQ(RunAndGet(src, "seen"), 15u);
}

// 18.5.11: a function called in a constraint is evaluated before the constraint
// is solved and its return value is used as a state variable — this holds even
// when the function's own argument is an ordinary (non-random) member rather
// than a random variable. Here inc(k) reads the non-random member k (set to 5
// by the constructor), so the function contributes the fixed value 6 and x is
// forced to it. No random variable is used as an argument, so no implicit
// ordering applies; the rule observed is purely that the call is made and its
// result drives the solve.
TEST(FunctionsInConstraints, FunctionOfStateVariableArgumentDrivesSolve) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int k;\n"
      "  function int inc(int a); return a + 1; endfunction\n"
      "  function new(); k = 5; endfunction\n"
      "  constraint cx { x == inc(k); }\n"
      "endclass\n"
      "module t;\n"
      "  int xv;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    xv = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "xv"), 6u);
}

// 18.5.11: the argument random variable may carry its own constraint, matching
// the clause's own example where the argument is a member of a small set and
// the consumer bounds a value built from the function of it. The argument y is
// restricted to {2, 4, 8} and x is bounded by 2*f(y); across many solves y only
// ever takes a value from its set and the consuming bound always holds, so the
// function-of-argument constraint is honored together with the argument's own
// membership constraint. The argument set is built from real 'inside' source
// syntax and the result is observed after randomize().
TEST(FunctionsInConstraints, SetConstrainedArgumentFeedsConsumer) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] y;\n"
      "  rand bit [7:0] x;\n"
      "  function int f(int a); return a; endfunction\n"
      "  constraint cy { y inside {2, 4, 8}; }\n"
      "  constraint cx { x <= 2 * f(y); }\n"
      "endclass\n"
      "module t;\n"
      "  int bad;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    bad = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (!(o.y == 2 || o.y == 4 || o.y == 8)) bad = bad + 1;\n"
      "      if (o.x > 2 * o.y) bad = bad + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Every solve honors both the argument's membership set and the consuming
  // bound built on the function of it.
  EXPECT_EQ(RunAndGet(src, "bad"), 0u);
}

// 18.5.11: a circular dependency created by the implicit ordering is an error
// even when the cycle is indirect. Three constraints each use the next
// variable as a function argument (a needs b, b needs c, c needs a), forming a
// three-hop cycle in the priority ordering. randomize() fails outright, the
// same outcome as a direct two-variable cycle — the ordering cannot be
// satisfied whatever its length.
TEST(FunctionsInConstraints, IndirectCircularArgumentOrderingFailsRandomize) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  rand bit [3:0] c;\n"
      "  function int id(int v); return v; endfunction\n"
      "  constraint cyc { a < id(b); b < id(c); c < id(a); }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

}  // namespace
