#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SolveBeforeOrdering, RandVariablesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit s;\n"
             "  rand bit [31:0] d;\n"
             "  constraint c { s -> d == 0; solve s before d; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

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

TEST(SolveBeforeOrdering, RealVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real r;\n"
             "  rand int y;\n"
             "  constraint c { solve r before y; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

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

TEST(SolveBeforeOrdering, ArraySizeMethodAcceptedElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  rand int n;\n"
             "  constraint c { solve A.size() before n; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SolveBeforeOrdering, CircularDependencyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a, b;\n"
             "  constraint c { solve a before b; solve b before a; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 3, "18.5.9"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 4, "18.5.9"));
}

TEST(SolveBeforeOrdering, AcyclicChainAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint k { solve a before b; solve b before c; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

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
