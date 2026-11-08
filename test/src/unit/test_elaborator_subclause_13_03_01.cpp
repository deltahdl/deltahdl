#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StaticAutomaticTask, AutoTaskItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

TEST(StaticAutomaticTask, StaticTaskItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task static t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StaticAutomaticTask, AutoTaskItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  initial y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

TEST(StaticAutomaticTask, AutoTaskItemHierRefInAnAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  initial assert (ok) y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 7,
      "13.3.1"));
}

TEST(StaticAutomaticTask, AutoTaskItemHierRefInAnAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic held;\n"
      "  logic armed;\n"
      "  task automatic drain();\n"
      "    int depth;\n"
      "  endtask\n"
      "  initial assert (armed) else held = drain.depth;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 7,
      "13.3.1"));
}

TEST(StaticAutomaticTask, AutoTaskItemHierRefInARandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic taken;\n"
      "  task automatic pick();\n"
      "    int chosen;\n"
      "  endtask\n"
      "  initial randcase 1: taken = pick.chosen; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

TEST(StaticAutomaticTask, AutoTaskItemHierRefInARandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic kept;\n"
      "  task automatic sample();\n"
      "    int sampled;\n"
      "  endtask\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = sample.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 8,
      "13.3.1"));
}

}  // namespace
