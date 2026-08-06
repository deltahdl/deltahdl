#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §18.17.7 governs value passing between randsequence productions. Data is
// passed down to a production through a formal argument list (bound like a task
// call and available throughout the production), and a production with a
// non-void return type returns a value that the triggering production reads
// through an implicit variable named after the production (an array indexed
// 1..N when the production appears more than once in the rule). All of this is
// generation-time behavior, so the subclause lives at the simulator stage
// (stmt_exec.cpp randsequence engine).

// §18.17.7: a production creates a scope encompassing all its rules and code
// blocks, so an argument passed down is available throughout the production —
// here read from two separate code blocks of the same production.
TEST(RandseqValuePassingSim, ArgumentAvailableThroughoutProduction) {
  SimFixture f;
  auto [a, b] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int a;\n"
                       "  int b;\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    randsequence(main)\n"
                       "      main : compute(9) ;\n"
                       "      compute( int v ) : { a = v; } { b = v + 1; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "a", "b");
  EXPECT_EQ(a, 9u);
  EXPECT_EQ(b, 10u);
}

// §18.17.7: when no actual argument is supplied, the formal's declared default
// value is used.
TEST(RandseqValuePassingSim, DefaultArgumentUsedWhenOmitted) {
  SimFixture f;
  uint64_t got = RunModule(f,
                           "module t;\n"
                           "  int got;\n"
                           "  initial begin\n"
                           "    got = 0;\n"
                           "    randsequence(main)\n"
                           "      main : compute ;\n"
                           "      compute( int v = 9 ) : { got = v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "got");
  EXPECT_EQ(got, 9u);
}

// §18.17.7: a production returns a value via 'return <expr>'; the triggering
// production reads it through an implicit variable named after the production.
TEST(RandseqValuePassingSim, ReturnValueReadByTriggeringProduction) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : a { r = a; } ;\n"
                         "      int a : { return 7; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 7u);
}

// §18.17.7: a production appearing more than once in a rule yields an implicit
// array indexed from 1 to the number of appearances, with element i holding the
// value returned by the i-th appearance in syntactic order. Here 'a' increments
// a counter and returns it, so a[1] precedes a[2], proving both the indexing
// and the left-to-right order in which return values become available.
TEST(RandseqValuePassingSim, MultipleAppearancesIndexedInSyntacticOrder) {
  SimFixture f;
  auto [r1, r2] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int n;\n"
                       "  int r1;\n"
                       "  int r2;\n"
                       "  initial begin\n"
                       "    n = 0; r1 = 0; r2 = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : a a { r1 = a[1]; r2 = a[2]; } ;\n"
                       "      int a : { n = n + 1; return n; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "r1", "r2");
  EXPECT_EQ(r1, 1u);
  EXPECT_EQ(r2, 2u);
}

// §18.17.7: a production that does not specify a return type assumes a void
// return type and so contributes no implicit return-value variable. Here the
// production named 'x' is void; inside main's code block the name 'x' therefore
// still resolves to the outer module variable (88) rather than to a
// return-value variable. Had 'x' been value-returning, an implicit local would
// have shadowed the outer 'x'.
TEST(RandseqValuePassingSim, NoReturnTypeProductionYieldsNoValue) {
  SimFixture f;
  uint64_t captured = RunModule(f,
                                "module t;\n"
                                "  int x;\n"
                                "  int captured;\n"
                                "  initial begin\n"
                                "    x = 88;\n"
                                "    captured = 0;\n"
                                "    randsequence(main)\n"
                                "      void main : x { captured = x; } ;\n"
                                "      x : { } ;\n"
                                "    endsequence\n"
                                "  end\n"
                                "endmodule\n",
                                "captured");
  EXPECT_EQ(captured, 88u);
}

// §18.17.7: data can be both passed down and returned up. A production accepts
// an argument, computes from it, and returns a value the parent reads back
// through the implicit variable named after the production.
TEST(RandseqValuePassingSim, ArgumentInThenValueOut) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : mk(10) { r = mk; } ;\n"
                         "      int mk( int base ) : { return base + 5; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

// §18.17.7: only the return values of productions already generated — those to
// the left of a code block — can be retrieved; a value not yet generated is not
// available. Here the production named 'a' is generated between two code
// blocks. The first code block runs before 'a' is generated, so no implicit
// return-value variable exists yet and the name 'a' still resolves to the outer
// module variable (99). The second code block runs after 'a' is generated, so
// 'a' there resolves to its return value (7). The contrast pins down the
// left-to-right availability rule deterministically.
TEST(RandseqValuePassingSim, OnlyAlreadyGeneratedValuesAreAvailable) {
  SimFixture f;
  // NB: `before` is a reserved keyword (Table B.1, e.g. solve..before), so it
  // cannot name a variable; use `pre` for the value captured ahead of `a`.
  auto [pre, after] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int a;\n"
                       "  int pre;\n"
                       "  int after;\n"
                       "  initial begin\n"
                       "    a = 99; pre = 0; after = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : { pre = a; } a { after = a; } ;\n"
                       "      int a : { return 7; } ;\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "pre", "after");
  // 'a' not yet generated -> outer variable; 'a' already generated -> its
  // value.
  EXPECT_EQ(pre, 99u);
  EXPECT_EQ(after, 7u);
}

// §18.17.7: more than one actual argument may be passed; the actuals bind to
// the formals by position, as in a task call.
TEST(RandseqValuePassingSim, MultipleArgumentsBoundByPosition) {
  SimFixture f;
  uint64_t got =
      RunModule(f,
                "module t;\n"
                "  int got;\n"
                "  initial begin\n"
                "    got = 0;\n"
                "    randsequence(main)\n"
                "      main : combine(3, 4) ;\n"
                "      combine( int a, int b ) : { got = a * 10 + b; } ;\n"
                "    endsequence\n"
                "  end\n"
                "endmodule\n",
                "got");
  EXPECT_EQ(got, 34u);
}

// §18.17.7: data is passed down to a production about to be generated
// regardless of how that production is reached. Here the production is selected
// by an rs_if production item, and its argument is still bound — exercising
// argument passing through the conditional-generation path.
TEST(RandseqValuePassingSim, ArgumentPassedThroughConditionalProduction) {
  SimFixture f;
  uint64_t got = RunModule(f,
                           "module t;\n"
                           "  int got;\n"
                           "  int sel;\n"
                           "  initial begin\n"
                           "    got = 0; sel = 1;\n"
                           "    randsequence(main)\n"
                           "      void main : pick ;\n"
                           "      pick : if (sel) hi(7) else lo(9) ;\n"
                           "      hi( int v ) : { got = v; } ;\n"
                           "      lo( int v ) : { got = v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "got");
  EXPECT_EQ(got, 7u);
}

// §18.17.7: each generation of a production gets its own scope, so two calls to
// the same production with different actuals each bind their own argument. Both
// generations run (no return type, so neither contributes a value), and their
// side effects accumulate the distinct arguments.
TEST(RandseqValuePassingSim, SeparateCallsBindOwnArguments) {
  SimFixture f;
  uint64_t sum = RunModule(f,
                           "module t;\n"
                           "  int sum;\n"
                           "  initial begin\n"
                           "    sum = 0;\n"
                           "    randsequence(main)\n"
                           "      void main : add(3) add(5) ;\n"
                           "      add( int v ) : { sum = sum + v; } ;\n"
                           "    endsequence\n"
                           "  end\n"
                           "endmodule\n",
                           "sum");
  EXPECT_EQ(sum, 8u);
}

// §18.17.7: actuals bind by position as in a task call, and a formal left
// unsupplied falls back to its declared default. Here only the first of two
// formals is supplied, so the second takes its default — exercising the
// boundary between positionally bound actuals and default-filled formals.
TEST(RandseqValuePassingSim, OmittedTrailingArgumentUsesDefault) {
  SimFixture f;
  uint64_t got =
      RunModule(f,
                "module t;\n"
                "  int got;\n"
                "  initial begin\n"
                "    got = 0;\n"
                "    randsequence(main)\n"
                "      main : combine(3) ;\n"
                "      combine( int a, int b = 5 ) : { got = a * 10 + b; } ;\n"
                "    endsequence\n"
                "  end\n"
                "endmodule\n",
                "got");
  EXPECT_EQ(got, 35u);
}

// §18.17.7: return values compose across nesting. A value-returning production
// reads the return value of a value-returning production it generated and
// returns a value of its own, which the top production then reads. This
// exercises the per-production return storage being saved and restored as
// generation nests.
TEST(RandseqValuePassingSim, NestedProductionReturnValues) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : outer { r = outer; } ;\n"
                         "      int outer : inner { return inner; } ;\n"
                         "      int inner : { return 3; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 3u);
}

}  // namespace
