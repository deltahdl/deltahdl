#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DesignBuildingBlockElaboration, PrecisionLessPreciseThanUnit) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, PrecisionEqualToUnit) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PrecisionFinerThanUnit) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, NoTimescaleElaboratesOk) {
  EXPECT_TRUE(ElabOk("module m; logic x; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PrecisionLongerByMagnitudeRejected) {
  ElabFixture ns_case;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 10ns;\n"
             "endmodule\n",
             ns_case));
  EXPECT_TRUE(ReportedError(ns_case.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
  ElabFixture ps_case;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 10ps;\n"
             "  timeprecision 100ps;\n"
             "endmodule\n",
             ps_case));
  EXPECT_TRUE(ReportedError(ps_case.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, PrecisionFinerByMagnitudeAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 100ps;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 10ns;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PackagePrecisionLessPreciseThanUnit) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endpackage\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, PackagePrecisionFinerThanUnitAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endpackage\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PackagePrecisionEqualToUnitAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ns;\n"
             "endpackage\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration,
     PackagePrecisionLongerByMagnitudeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 10ns;\n"
             "endpackage\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, UninstantiatedInterfacePrecisionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("interface intf;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endinterface\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, UninstantiatedInterfacePrecisionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface intf;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endinterface\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, UninstantiatedProgramPrecisionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("program prog;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endprogram\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, UninstantiatedProgramPrecisionAccepted) {
  EXPECT_TRUE(
      ElabOk("program prog;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endprogram\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, LoneTimeunitEqualToDefaultPrecision) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, LoneTimeunitFinerThanDefaultPrecision) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ps;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, LoneTimeprecisionCoarserThanDefaultUnit) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeprecision 10ns;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

TEST(DesignBuildingBlockElaboration, LoneTimeunitTakesTheTimescalePrecision) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, LoneTimeunitFinerThanTimescalePrecision) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`timescale 1ns / 10ps\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            2, "3.14"));
}

TEST(DesignBuildingBlockElaboration, LoneTimeprecisionCoarserThanCuTimeunit) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("timeunit 1ps;\n"
             "timeprecision 1ps;\n"
             "module m;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            3, "3.14"));
}

TEST(DesignBuildingBlockElaboration, CuTimeunitFinerThanDefaultPrecision) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("timeunit 1ps;\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            2, "3.14"));
}

TEST(DesignBuildingBlockElaboration, CuPrecisionCoarserThanCuUnit) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("timeunit 1ps;\n"
             "timeprecision 1ns;\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            3, "3.14"));
}

TEST(DesignBuildingBlockElaboration, NestedLoneTimeunitInheritsPrecision) {
  EXPECT_TRUE(
      ElabOk("module outer;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ps;\n"
             "  module inner;\n"
             "    timeunit 1ps;\n"
             "  endmodule\n"
             "  inner i();\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, NestedLoneTimeunitFinerThanInherited) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module outer;\n"
             "  timeunit 10ps;\n"
             "  timeprecision 10ps;\n"
             "  module inner;\n"
             "    timeunit 1ps;\n"
             "  endmodule\n"
             "  inner i();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            4, "3.14"));
}

TEST(DesignBuildingBlockElaboration,
     NestedLoneTimeprecisionCoarserThanInherited) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module outer;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ns;\n"
             "  module inner;\n"
             "    timeprecision 10ns;\n"
             "  endmodule\n"
             "  inner i();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            4, "3.14"));
}

TEST(DesignBuildingBlockElaboration, PackageLoneTimeunitFinerThanDefault) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  timeunit 1ps;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            1, "3.14"));
}

}  // namespace
