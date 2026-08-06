#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive variable ordering (18.5.9) end to end: each source program
// declares a class with rand variables and a 'solve ... before ...' ordering
// constraint, calls randomize() from an initial block in a loop, and copies the
// observed frequencies out to module variables the harness reads. The parser
// captures the ordering into constraint_solve_before_refs, the elaborator
// enforces the variable restrictions, and the simulator lowers each reference
// into the solver's variable ordering. The behavior observed here is therefore
// that of real elaborated source, not a hand-built solver state. The variables
// are declared rand per 18.4.1, the dependency this pass builds its inputs on.

// 18.5.9: with no ordering constraint the solver gives a uniform distribution
// over the legal value combinations — every legal (s, d) pair is equally
// probable. For the 's -> d == 0' example with a 2-bit d there are five legal
// combinations {(0,0),(0,1),(0,2),(0,3),(1,0)} and s is 1 in only one of them,
// so without ordering s comes out 1 with probability near 1/5. The
// far-from-half frequency is what the ordering example then sets out to change.
TEST(VariableOrdering, UniformOverLegalCombinationsWithoutOrdering) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ones;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    ones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) ones = ones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ~120 (1/5 of 600); a wide band keeps the statistical test stable
  // while still excluding the ordered ~1/2 behavior.
  auto ones = RunAndGet(src, "ones");
  EXPECT_GE(ones, 50u);
  EXPECT_LE(ones, 210u);
}

// 18.5.9: 'solve s before d' instructs the solver to choose s before d. The
// effect is that s is now chosen 0 or 1 with 50/50 probability, and d is then
// chosen subject to the value of s. The set of legal combinations is unchanged,
// but s is 1 about half the time rather than about a fifth — the distribution
// the ordering is meant to produce, and the observable that proves the ordering
// statement is carried from source into the solver.
TEST(VariableOrdering, SolveBeforeShiftsDistributionTowardOrderedVariable) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int ones;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    ones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) ones = ones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ~300 (1/2 of 600), clearly separated from the ~120 of the
  // unordered case.
  auto ones = RunAndGet(src, "ones");
  EXPECT_GE(ones, 240u);
  EXPECT_LE(ones, 360u);
}

// 18.5.9: a 'solve ... before ...' constraint does not change the solution
// space. Every assignment the ordered solve produces is one of the same legal
// combinations the unordered solve admits — both an s=0 result and the s=1
// (with d=0) result still occur, and no illegal (s=1, d!=0) pair is ever
// produced.
TEST(VariableOrdering, OrderingPreservesSolutionSpace) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    int saw0 = 0; int saw1 = 0; int bad = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) begin\n"
      "        saw1 = 1;\n"
      "        if (o.d != 0) bad = 1;\n"
      "      end else saw0 = 1;\n"
      "    end\n"
      "    good = (saw0 && saw1 && !bad) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.9: a 'solve ... before ...' constraint cannot cause the solver to fail —
// it reweights probabilities but never removes a solution. Even with the
// ordering in place, the satisfiable constraint set is solved on every
// randomization.
TEST(VariableOrdering, OrderingNeverCausesFailure) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      if (o.randomize() == 0) allok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
}

// 18.5.9: a variable that is not explicitly ordered is solved with the last set
// of ordered variables — after the ordered head — so its value is conditioned
// on the earlier choice rather than chosen freely. With 'solve a before d', the
// head a is drawn first and keeps a uniform 1/2 marginal, while the unnamed u
// (constrained by 'u -> a == 0') is solved afterward: u can be 1 only when a
// happened to be 0, giving a skewed ~1/4 marginal. Both marginals differ from
// the ~1/3 they would share were there no ordering, showing u is solved last
// (after a), not first. The same source is run twice, reading each marginal in
// turn.
TEST(VariableOrdering, UnorderedVariableSolvedWithLastSet) {
  const char* src =
      "class B;\n"
      "  rand bit a;\n"
      "  rand bit d;\n"
      "  rand bit u;\n"
      "  constraint c { u -> a == 0; }\n"
      "  constraint ord { solve a before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int aones; int uones;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    aones = 0; uones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.a == 1) aones = aones + 1;\n"
      "      if (o.u == 1) uones = uones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // a is the ordered head: drawn first, uniform near 1/2 (~300), above the ~200
  // it would show without ordering.
  auto aones = RunAndGet(src, "aones");
  EXPECT_GE(aones, 240u);
  EXPECT_LE(aones, 360u);
  // u is unordered, solved with the last set and conditioned on a: near 1/4
  // (~150), clearly below the ~200 it would show if it were solved first.
  auto uones = RunAndGet(src, "uones");
  EXPECT_GE(uones, 90u);
  EXPECT_LE(uones, 195u);
}

// 18.5.9: variables that are only partially ordered are solved with the latest
// set of ordered variables such that all ordering constraints are still met.
// Here a and b are each ordered before c ('solve a before c; solve b before
// c;') but are mutually unordered, so each is partially ordered. They are
// therefore solved with the latest set that keeps them ahead of c — the set
// drawn before c — so each keeps a free uniform ~1/2 marginal, while the wide
// dependent c is solved last. The constraints 'a -> c == 0' and 'b -> c == 0'
// force c to 0 whenever either control is 1, so without ordering the
// joint-uniform draw would pull a toward 0 (a is 1 in only 2 of the 7 legal
// combinations, ~2/7). Solving a and b in the set before c instead gives each a
// free 1/2 marginal — the shift that proves they are placed in the earlier
// ordered set. The same source is read twice: once for the partially ordered
// head's marginal, once to confirm the ordering constraints are met on every
// draw.
TEST(VariableOrdering, PartiallyOrderedVariablesSolvedWithLatestSet) {
  const char* src =
      "class B;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit [1:0] c;\n"
      "  constraint dep { a -> c == 0; b -> c == 0; }\n"
      "  constraint ord { solve a before c; solve b before c; }\n"
      "endclass\n"
      "module t;\n"
      "  int aones; int ok;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    aones = 0; ok = 1;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      if (o.randomize() == 0) ok = 0;\n"
      "      if (o.a == 1) aones = aones + 1;\n"
      "      if ((o.a || o.b) && o.c != 0) ok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // a is partially ordered and solved with the set drawn before c, so it keeps
  // a free uniform ~1/2 marginal (~300 of 600), well above the ~171 (2/7) the
  // joint-uniform unordered draw would give.
  auto aones = RunAndGet(src, "aones");
  EXPECT_GE(aones, 240u);
  EXPECT_LE(aones, 360u);
  // Every draw solves and honors the ordering constraints: no failure, and c is
  // 0 whenever a or b is 1.
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
}

}  // namespace
