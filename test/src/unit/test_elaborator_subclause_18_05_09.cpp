#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.5.9: only random variables are allowed in a solve...before ordering — they
// shall be rand. Ordering two rand variables is within that rule and
// elaborates.
TEST(SolveBeforeOrdering, RandVariablesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit s;\n"
             "  rand bit [31:0] d;\n"
             "  constraint c { s -> d == 0; solve s before d; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.9: a non-random (state) variable may not be ordered. Naming a plain
// (non-rand) member in a solve...before list is an error.
TEST(SolveBeforeOrdering, NonRandVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  rand int y;\n"
             "  constraint c { solve x before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'x' is not a random variable and cannot appear "
                            "in a solve...before ordering constraint",
                            4, "18.5.9"));
}

// 18.5.9: randc variables are not allowed in a solve...before ordering — they
// are always solved before any other variable. Naming a randc member is an
// error.
TEST(SolveBeforeOrdering, RandcVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { solve x before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randc variable 'x' is not allowed in a "
                            "solve...before ordering constraint",
                            4, "18.5.9"));
}

// 18.5.9: the rule applies to the after-list as well as the before-list, so a
// randc variable named after 'before' is equally an error.
TEST(SolveBeforeOrdering, RandcVariableInAfterListRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { solve y before x; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randc variable 'x' is not allowed in a "
                            "solve...before ordering constraint",
                            4, "18.5.9"));
}

// 18.5.9: the ordered variables shall be integral or real. A real rand variable
// is allowed as an ordering variable.
TEST(SolveBeforeOrdering, RealVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real r;\n"
             "  rand int y;\n"
             "  constraint c { solve r before y; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.9: the ordered variables shall be integral or real. A rand object handle
// is neither, so ordering it is an error.
TEST(SolveBeforeOrdering, ObjectHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class P; endclass\n"
             "class C;\n"
             "  rand P p;\n"
             "  rand int y;\n"
             "  constraint c { solve p before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "solve...before ordering variable 'p' shall be of "
                            "integral or real type",
                            5, "18.5.9"));
}

// 18.5.9: array.size is expressly allowed as an ordering variable, so an
// array-method primary such as A.size() is accepted even though 'size' is not a
// declared rand member. This is the elaboration-stage claim; the parser file
// for this subclause carries the matching grammar case.
TEST(SolveBeforeOrdering, ArraySizeMethodAcceptedElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  rand int n;\n"
             "  constraint c { solve A.size() before n; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.9: there shall be no circular dependency in the ordering. 'solve a
// before b' combined with 'solve b before a' forms a cycle and is an error.
TEST(SolveBeforeOrdering, CircularDependencyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a, b;\n"
             "  constraint c { solve a before b; solve b before a; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  // The report names no variable, so its line is what ties it to this source:
  // SolveBeforeOrdering::report_loc is set from the first 'solve' keyword the
  // class carries (elaborator_validate_class_constraints.cpp:522-525), and both
  // orderings here stand on line 3.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 3, "18.5.9"));
}

// 18.5.9: a longer cycle spanning three ordering statements is likewise an
// error: a before b, b before c, c before a.
TEST(SolveBeforeOrdering, ThreeNodeCircularDependencyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint k {\n"
             "    solve a before b;\n"
             "    solve b before c;\n"
             "    solve c before a;\n"
             "  }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  // Line 4 is 'solve a before b;', the first of the three orderings, which is
  // the one SolveBeforeOrdering::report_loc keeps; the cycle is closed on
  // line 6, so the line asserted here also says the report anchors on the
  // first reference rather than on the closing one.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 4, "18.5.9"));
}

// 18.5.9: a partial order with no cycle is legal. A chain a before b before c
// elaborates.
TEST(SolveBeforeOrdering, AcyclicChainAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint k { solve a before b; solve b before c; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.9: the no-circular-dependency rule also rejects the degenerate case
// where a variable is ordered before itself — naming the same variable on both
// sides of one solve statement is a self-cycle.
TEST(SolveBeforeOrdering, SelfOrderingRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  constraint c { solve a before a; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 3, "18.5.9"));
}

}  // namespace
