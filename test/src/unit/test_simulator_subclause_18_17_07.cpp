#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_string_var.h"
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

// §18.17.7: the implicit variable is declared for each value-returning
// production the rule names, including one named inside an if production. The
// clause's second example gives the code block of `if (cond) D(5) else D(20)`
// the declaration `int D[1:2]`, so the true branch's generation is element 1.
// A rule that only counted the productions written directly in it declares no
// variable named mk at all, and the code block then reads nothing.
TEST(RandseqValuePassingSim, IfBranchProductionWritesTheFirstImplicitElement) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int cond;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    cond = 1;\n"
                         "    randsequence(main)\n"
                         "      void main : if (cond) mk(5) else mk(20)\n"
                         "                  { r = mk[1]; } ;\n"
                         "      int mk (int v) : { return v; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 5u);
}

// §18.17.7: the element an appearance writes is fixed by where the appearance
// is written, not by the order in which generation reached it. Of the same
// `if (cond) D(5) else D(20)`, the clause says the second element is assigned
// the value returned by D(20) when cond is false — although the else branch is
// then the only appearance that generated at all. An engine numbering the
// elements as it generates writes element 1 here and leaves element 2 at zero.
TEST(RandseqValuePassingSim,
     ElseBranchProductionWritesTheSecondImplicitElement) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int cond;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    cond = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : if (cond) mk(5) else mk(20)\n"
                         "                  { r = mk[2]; } ;\n"
                         "      int mk (int v) : { return v; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 20u);
}

// §18.17.7: a repeat production names its item once however many times it
// generates it, so the implicit variable is the scalar named after the
// production and each generation overwrites it. The clause's second example
// gives the code block of `B repeat(5) C B` the declarations `int B[1:2]` and
// `int C`, the scalar for the repeated C. Three generations each increment n
// and return it, so the scalar holds 3 rather than the 1 a single generation
// would leave or the zero an unwritten variable would.
TEST(RandseqValuePassingSim,
     RepeatedProductionWritesOneScalarImplicitVariable) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int n;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    n = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : repeat(3) c { r = c; } ;\n"
                         "      int c : { n = n + 1; return n; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 3u);
}

// §18.17.7: a production named by a case item is named by the rule, so it too
// gets an implicit variable. The two productions here return different values
// and each is named once, so each variable is a scalar; the code block reads
// the one the case selected. A rule that only counted its directly written
// items declares neither, and the block reads nothing.
TEST(RandseqValuePassingSim, CaseItemProductionWritesItsImplicitVariable) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  int sel;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    sel = 2;\n"
                         "    randsequence(main)\n"
                         "      void main : case (sel) 1 : p1; 2 : p2;\n"
                         "                  endcase { r = p2; } ;\n"
                         "      int p1 : { return 3; } ;\n"
                         "      int p2 : { return 7; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 7u);
}

// §18.17.7: the return statement assigns its expression to the production whose
// code block holds it. `inner` declares no return type, so its `return 9` names
// no production to assign to and `outer` keeps the zero it was generated with;
// the code block reads outer + 1 and so distinguishes that zero from the 55 the
// variable held before the randsequence. An engine that lets a void production
// keep the return slot of the production that triggered it reports 10 here,
// because inner's returned expression lands in outer's value.
TEST(RandseqValuePassingSim,
     VoidProductionReturnLeavesTheTriggeringValueAlone) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 55;\n"
                         "    randsequence(main)\n"
                         "      void main : outer { r = outer + 1; } ;\n"
                         "      int outer : inner ;\n"
                         "      void inner : { return 9; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

// §18.17.7: a production may declare a string return type -- the subclause's
// first example declares `string operator`, whose rules return "+", "-" and
// "*" -- and the triggering production reads that value through the implicit
// variable named after the production. The value has to be a string and not
// just the bits of one: a bare $display argument is rendered as its characters
// only when the value is marked a string (eval_system_task.cpp,
// AppendDisplayArg picking 's' over the task's default radix), so an unmarked
// value prints the decimal 43 here instead of "+". Only one rule is written, so
// the returned text is fixed rather than drawn at random.
TEST(RandseqValuePassingSim, StringReturnTypeProductionCarriesItsText) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r;\n"
      "  initial begin\n"
      "    r = \"unset\";\n"
      "    randsequence(main)\n"
      "      void main : op { r = op; $display(op); } ;\n"
      "      string op : { return \"+\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "+\n");
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "+");
}

// §18.17.7: a production named more than once in a rule yields an implicit
// array indexed 1..N whose element type is the production's return type, so
// each element of a string production's array is itself a string. An element
// is reached by a select rather than by the production's bare name, so what
// marks it a string is not what marks the scalar, and it can go unmarked on its
// own: an unmarked element prints as decimal digits. The formal `k` fixes which
// text each appearance returns, so neither element depends on a random choice.
TEST(RandseqValuePassingSim, StringReturnTypeArrayElementsCarryTheirText) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r1;\n"
      "  string r2;\n"
      "  initial begin\n"
      "    r1 = \"unset\"; r2 = \"unset\";\n"
      "    randsequence(main)\n"
      "      void main : op(1) op(2)\n"
      "                  { r1 = op[1]; r2 = op[2];\n"
      "                    $display(op[1]); $display(op[2]); } ;\n"
      "      string op ( int k ) :\n"
      "        { if (k == 1) return \"minus\"; return \"times\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "minus\ntimes\n");
  auto* first = f.ctx.FindVariable("r1");
  auto* second = f.ctx.FindVariable("r2");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(VecToStr(first->value), "minus");
  EXPECT_EQ(VecToStr(second->value), "times");
}

// §18.17.7: the implicit variable holds a string, so it answers the string
// methods §6.16.1 gives one. `op.len()` resolves only for a variable the
// simulation context knows to be a string (eval_string.cpp,
// TryEvalStringMethodCall), so it reports the nine characters of "plusminus"
// only once the production's value is registered as one. Nine characters also
// outrun the four that fit in the 32 bits an integer return type would take,
// so the printed text distinguishes a full value from a truncated one -- which
// a one-character return cannot do.
TEST(RandseqValuePassingSim, StringReturnLongerThanFourCharactersSurvives) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  string r;\n"
      "  int n;\n"
      "  initial begin\n"
      "    r = \"unset\"; n = 0;\n"
      "    randsequence(main)\n"
      "      void main : op { r = op; n = op.len(); $display(op); } ;\n"
      "      string op : { return \"plusminus\"; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "plusminus\n");
  auto* text = f.ctx.FindVariable("r");
  auto* len = f.ctx.FindVariable("n");
  ASSERT_NE(text, nullptr);
  ASSERT_NE(len, nullptr);
  EXPECT_EQ(VecToStr(text->value), "plusminus");
  EXPECT_EQ(len->value.ToUint64(), 9u);
}

// §18.17: "The randsequence statement creates an automatic scope." What
// §18.17.7 implicitly declares inside a rule is declared in that scope, so
// nothing it declared can still be read once the statement has ended. Here the
// rule names the value-returning production 'a' twice, which §18.17.7 declares
// as `int a[1:2]` for the rule's code block, and the module declares a
// variable of its own named 'a'. After the randsequence, `a[1]` is a bit-select
// of that module variable per §11.5.1 and reads bit 1 of 8'b1010_1010, which
// is 1. A shape recorded under the bare name 'a' and left standing reads the
// same expression as element 1 of an array whose elements are gone, which is x
// and so 0. The read has to come after the randsequence: one taken before it
// reads the module variable whether the shape leaks or not, and so cannot
// fail.
TEST(RandseqValuePassingSim, ImplicitArrayShapeDoesNotOutliveTheStatement) {
  SimFixture f;
  auto [in_rule, after] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic [7:0] a;\n"
                       "  int n;\n"
                       "  int in_rule;\n"
                       "  int after;\n"
                       "  initial begin\n"
                       "    a = 8'b1010_1010;\n"
                       "    n = 0; in_rule = 0; after = 0;\n"
                       "    randsequence(main)\n"
                       "      void main : a a { in_rule = a[2]; } ;\n"
                       "      int a : { n = n + 1; return n; } ;\n"
                       "    endsequence\n"
                       "    after = a[1];\n"
                       "  end\n"
                       "endmodule\n",
                       "in_rule", "after");
  // Inside the rule 'a' is the implicit array, so a[2] is its second element;
  // after the statement 'a' is the module variable, so a[1] is its bit 1.
  EXPECT_EQ(in_rule, 2u);
  EXPECT_EQ(after, 1u);
}

// §18.17 gives each randsequence statement an automatic scope of its own, so
// what one statement implicitly declared is gone before the next one runs.
// §18.17.7: "If a production appears only once in a rule, the type of the
// implicit variable is the return type of the production" -- a scalar. The
// first statement's rule names 'p' twice and so declares `int p[1:2]`; the
// second statement's rule names 'p' once and so declares the scalar `int p`,
// whose `p[1]` is a bit-select per §11.5.1 and reads bit 1 of 6, which is 1. A
// shape left standing by the first statement reads the same expression as
// element 1 of an array whose elements are gone, which is x and so 0. Naming
// 'p' once in the second statement is what lets the leak show: a rule naming it
// more than once records a shape of its own over the stale one, so the order
// that puts the count of one last is the only one that can fail.
TEST(RandseqValuePassingSim,
     ImplicitArrayShapeDoesNotReachTheNextRandsequence) {
  SimFixture f;
  auto [total, sel] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int total;\n"
      "  int sel;\n"
      "  initial begin\n"
      "    total = 0; sel = 0;\n"
      "    randsequence(main)\n"
      "      void main : p(20) p(30) { total = p[1] + p[2]; } ;\n"
      "      int p ( int k ) : { return k; } ;\n"
      "    endsequence\n"
      "    randsequence(main)\n"
      "      void main : p(6) { sel = p[1]; } ;\n"
      "      int p ( int k ) : { return k; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "total", "sel");
  // 20 and 30 are the first statement's two elements; neither is 1, so a read
  // that reached them instead of bit 1 of the scalar is still distinguishable.
  EXPECT_EQ(total, 50u);
  EXPECT_EQ(sel, 1u);
}

// §18.17.7's Example 2 gives one production ('C') rules that name it once,
// twice and three times over, so the implicit variable's shape belongs to the
// rule that named the production and not to the production itself. §18.17 makes
// every activation's scope automatic and says "a recursive production will
// cause looping", so an inner activation's declarations are gone once it
// returns. Here 'main' names 'p' twice, declaring `int p[1:2]` for main's code
// block, while 'p' names itself three times, declaring `int p[1:3]` for its
// own. After the inner activations have returned, %p prints main's array as an
// assignment pattern of its elements per §21.2.1.6, which is two of them. A
// shape recorded under the bare name 'p' and left standing by the inner
// activations prints three, the third an element main never declared and
// nothing ever wrote. One activation deep cannot tell the two apart, since the
// only shape recorded is then the one being read.
TEST(RandseqValuePassingSim, RecursiveActivationLeavesTheOuterArrayShape) {
  SimFixture f;
  auto printed = RunCapture(
      "module t;\n"
      "  int total;\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    randsequence(main)\n"
      "      void main : p(1) p(2)\n"
      "                  { total = p[1] + p[2]; $display(\"%p\", p); } ;\n"
      "      int p ( int d ) : if (d) p(0) if (d) p(0) if (d) p(0)\n"
      "                        { return d + 40; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "'{41, 42}\n");
  // The elements themselves are read back too, so a run that printed the right
  // pattern for the wrong reason -- because no element was generated at all --
  // is still caught.
  auto* sum = f.ctx.FindVariable("total");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 83u);
}

}  // namespace
