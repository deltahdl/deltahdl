#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SoftConstraintVariable, SoftOnRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { soft x == 3; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SoftConstraintVariable, SoftOnRandcVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { soft x == 3; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a soft constraint may not be specified on randc variable 'x'", 4,
      "18.5.13.1"));
}

TEST(SoftConstraintVariable, SoftOnRandcInSetMembershipRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft x inside {[1:2]}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a soft constraint may not be specified on randc variable 'x'", 3,
      "18.5.13.1"));
}

TEST(SoftConstraintVariable, SoftDistOnRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { soft x dist {1 := 1, 2 := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SoftConstraintVariable, SoftDistOnRandcVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft x dist {1 := 1, 2 := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a soft constraint may not be specified on randc variable 'x'", 3,
      "18.5.13.1"));
}

TEST(SoftConstraintVariable, RandcInHardConstraintNotFlagged) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { x < y; soft y == 3; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SoftConstraintVariable, RandcInHardConstraintAfterSoftNotFlagged) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft y == 3; x < y; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SoftConstraintVariable, RandcInLaterSoftConstraintRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { soft y == 1; soft x == 2; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a soft constraint may not be specified on randc variable 'x'", 4,
      "18.5.13.1"));
}

TEST(SoftConstraintVariable, SoftOnInheritedRandcRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc bit [3:0] cy;\n"
             "endclass\n"
             "class D extends B;\n"
             "  rand int r;\n"
             "  constraint c { soft cy < r; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a soft constraint may not be specified on randc variable 'cy'", 6,
      "18.5.13.1"));
}

}  // namespace
