#include <gtest/gtest.h>

#include <string>

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

void ExpectDistReport(const std::string& src, const std::string& msg,
                      int line) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, line, "18.5.3")) << src;
}

void ExpectDistAccepted(const std::string& src) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(src, f)) << src;
}

std::string ClassWith(const std::string& decls, const std::string& item) {
  return "class C;\n" + decls + "  constraint c { " + item +
         " }\n"
         "endclass\n"
         "module m;\n"
         "endmodule\n";
}

std::string ExternalWith(const std::string& decls, const std::string& item) {
  return "class C;\n" + decls +
         "  constraint c;\n"
         "endclass\n"
         "constraint C::c { " +
         item +
         " }\n"
         "module m;\n"
         "endmodule\n";
}

std::string InlineWith(const std::string& decls, const std::string& item) {
  return "class C;\n" + decls +
         "endclass\n"
         "module m;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    void'(o.randomize() with { " +
         item +
         " });\n"
         "  end\n"
         "endmodule\n";
}

const char* const kNoRand =
    "a dist expression shall contain at least one rand variable";
const char* const kXY =
    "  int x;\n"
    "  rand int y;\n";

TEST(DistNeedsRand, DISABLED_AStateVariableAloneIsReported) {
  ExpectDistReport(ClassWith(kXY, "x dist {10 := 1, 20 := 1};"), kNoRand, 4);
}

TEST(DistNeedsRand, DISABLED_AnExpressionOfStateAndConstantsIsReported) {
  ExpectDistReport(ClassWith(kXY, "x + 1 dist {10 := 1};"), kNoRand, 4);
}

TEST(DistNeedsRand, DISABLED_AnExternalBlockIsChecked) {
  ExpectDistReport(ExternalWith(kXY, "x dist {10 := 1};"), kNoRand, 6);
}

TEST(DistNeedsRand, DISABLED_AnInlineBlockIsChecked) {
  ExpectDistReport(InlineWith(kXY, "x dist {10 := 1};"), kNoRand, 8);
}

TEST(DistNeedsRand, AnExpressionHoldingARandVariableIsAccepted) {
  ExpectDistAccepted(ClassWith(kXY, "y dist {10 := 1, 20 := 1};"));
  ExpectDistAccepted(ClassWith(kXY, "x + y dist {10 := 1};"));
  ExpectDistAccepted(InlineWith(kXY, "x + y dist {10 := 1};"));
}

const char* const kRandcB =
    "a dist constraint may not be applied to randc variable 'b'";
const char* const kAB =
    "  rand bit [3:0] a;\n"
    "  randc bit [3:0] b;\n";

TEST(DistOnRandc, AnExternalBlockIsChecked) {
  ExpectDistReport(ExternalWith(kAB, "b dist {3 := 1, 4 := 1};"), kRandcB, 6);
}

TEST(DistOnRandc, DISABLED_AnInlineBlockIsChecked) {
  ExpectDistReport(InlineWith(kAB, "b dist {3 := 1, 4 := 1};"), kRandcB, 8);
}

TEST(DistOnRandc, DISABLED_ARandcInsideTheExpressionIsReported) {
  ExpectDistReport(ClassWith(kAB, "a + b dist {3 := 1, 4 := 1};"), kRandcB, 4);
}

TEST(DistOnRandc, DISABLED_ARandcArrayElementInAForeachIsReported) {
  ExpectDistReport(ClassWith("  randc bit [3:0] b[2];\n",
                             "foreach (b[i]) b[i] dist {3 := 1, 4 := 1};"),
                   kRandcB, 4);
}

TEST(DistOnRandc, DISABLED_ASoftDistIsReported) {
  ExpectDistReport(ClassWith(kAB, "soft b dist {3 := 1, 4 := 1};"), kRandcB, 4);
}

TEST(DistOnRandc, ARandVariableBesideItIsAccepted) {
  ExpectDistAccepted(ClassWith(kAB, "a dist {3 := 1, 4 := 1};"));
  ExpectDistAccepted(InlineWith(kAB, "a dist {3 := 1, 4 := 1};"));
}

const char* const kRealRange =
    "a real-valued range in a dist constraint requires the :/ operator and an "
    "explicit weight";
const char* const kRealA = "  rand real a;\n";

TEST(RealDistRange, AnExternalBlockIsChecked) {
  ExpectDistReport(ExternalWith(kRealA, "a dist {[1.0:3.0] := 1};"), kRealRange,
                   5);
  ExpectDistReport(ExternalWith(kRealA, "a dist {[1.0:3.0]};"), kRealRange, 5);
}

TEST(RealDistRange, DISABLED_AnInlineBlockIsChecked) {
  ExpectDistReport(InlineWith(kRealA, "a dist {[1.0:3.0] := 1};"), kRealRange,
                   7);
  ExpectDistReport(InlineWith(kRealA, "a dist {[1.0:3.0]};"), kRealRange, 7);
}

TEST(RealDistRange, DISABLED_AScopeRandomizeInlineBlockIsChecked) {
  for (const char* item : {"[1.0:3.0] := 1", "[1.0:3.0]"}) {
    ExpectDistReport(
        std::string("module m;\n"
                    "  real a;\n"
                    "  initial begin\n"
                    "    void'(std::randomize(a) with { a dist {") +
            item +
            "}; });\n"
            "  end\n"
            "endmodule\n",
        kRealRange, 4);
  }
}

TEST(RealDistRange, ASecondRangeWithoutAWeightIsReported) {
  ExpectDistReport(ClassWith(kRealA, "a dist {[1.0:3.0] :/ 1, [4.0:5.0]};"),
                   kRealRange, 3);
}

TEST(RealDistRange, ClassesInAPackageAndAModuleAreChecked) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class C;\n"
      "    rand real a;\n"
      "    constraint c { a dist {[1.0:3.0] := 1}; }\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class D;\n"
      "    rand real a;\n"
      "    constraint c { a dist {[1.0:3.0]}; }\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kRealRange, 4, "18.5.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kRealRange, 10, "18.5.3"));
}

TEST(RealDistRange, AnInlineRangeWithADivideWeightIsAccepted) {
  ExpectDistAccepted(InlineWith(kRealA, "a dist {[1.0:3.0] :/ 1};"));
}

}  // namespace
