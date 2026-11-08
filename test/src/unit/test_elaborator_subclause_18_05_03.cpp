#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealDistRange, DivideOperatorWithWeightAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0] :/ 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RealDistRange, AssignOperatorRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a real-valued range in a dist constraint requires "
                            "the :/ operator and an explicit weight",
                            3, "18.5.3"));
}

TEST(RealDistRange, MissingWeightRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  constraint c { a dist {[1.0:3.0]}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a real-valued range in a dist constraint requires "
                            "the :/ operator and an explicit weight",
                            3, "18.5.3"));
}

TEST(RealDistRange, IntegralRangeWithAssignAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x dist {[1:3] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RealDistRange, InheritedRealTargetChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  rand real a;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { a dist {[1.0:3.0] := 1}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a real-valued range in a dist constraint requires "
                            "the :/ operator and an explicit weight",
                            5, "18.5.3"));
}

TEST(DistOnRandc, RandcTargetRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class a;\n"
             "  randc int b;\n"
             "  constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a dist constraint may not be applied to randc variable 'b'", 3,
      "18.5.3"));
}

TEST(DistOnRandc, RandTargetAccepted) {
  EXPECT_TRUE(
      ElabOk("class a;\n"
             "  rand int b;\n"
             "  constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(DistOnRandc, InheritedRandcTargetRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc int b;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a dist constraint may not be applied to randc variable 'b'", 5,
      "18.5.3"));
}

TEST(DistOnRandc, ModuleScopedClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  class a;\n"
             "    randc int b;\n"
             "    constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a dist constraint may not be applied to randc variable 'b'", 4,
      "18.5.3"));
}

TEST(DistOnRandc, PackageScopedClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  class a;\n"
             "    randc int b;\n"
             "    constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "  endclass\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a dist constraint may not be applied to randc variable 'b'", 4,
      "18.5.3"));
}

TEST(DistOnRandc, NestedClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    randc int b;\n"
             "    constraint c { b dist {3 := 0, 10 := 5}; }\n"
             "  endclass\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a dist constraint may not be applied to randc variable 'b'", 4,
      "18.5.3"));
}

}  // namespace
