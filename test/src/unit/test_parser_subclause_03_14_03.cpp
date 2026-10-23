#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_reported_error.h"
#include "parser/time_resolve.h"

using namespace delta;
namespace {

TEST(DesignBuildingBlockParsing, ConsidersTimescalePrec) {
  auto r = PreprocessAndParse(
      "`timescale 1ns / 1ps\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, MinAcrossAllThreeSources) {
  auto r = PreprocessAndParse(
      "`timescale 1us / 1ns\n"
      "module a;\n"
      "  timeunit 1ms / 1us;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, DefaultWhenNoneSpecified) {
  auto r = PreprocessAndParse(
      "module a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, CUScopeTimeprecisionIncluded) {
  auto r = PreprocessAndParse(
      "timeprecision 1fs;\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, InterfacesAndProgramsContribute) {
  auto r = PreprocessAndParse(
      "interface i;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n"
      "program p;\n"
      "  timeprecision 1ns;\n"
      "endprogram\n"
      "module m;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, MinOfTimeprecisionStatements) {
  auto r = PreprocessAndParse(
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module c;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, ConsidersTimeunitPrecArg) {
  auto r = PreprocessAndParse(
      "module a;\n"
      "  timeunit 1us / 1fs;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, PackageTimeprecisionContributes) {
  auto r = PreprocessAndParse(
      "package p;\n"
      "  timeprecision 1fs;\n"
      "endpackage\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, PackageTimeunitPrecArgContributes) {
  auto r = PreprocessAndParse(
      "package p;\n"
      "  timeunit 1us / 1fs;\n"
      "endpackage\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeunit) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "step cannot be used to set or modify the time unit or precision", 2,
      "3.14.3"));
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeprecision) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeprecision 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "step cannot be used to set or modify the time unit or precision", 2,
      "3.14.3"));
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeunitPrecArg) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns / 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "step cannot be used to set or modify the time unit or precision", 2,
      "3.14.3"));
}

TEST(DesignBuildingBlockParsing, TimeunitWithoutPrecArgDoesNotContribute) {
  auto r = PreprocessAndParse(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1fs;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, StepRejectedInPackageTimeunit) {
  auto r = PreprocessAndParse(
      "package p;\n"
      "  timeunit 1step;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "step cannot be used to set or modify the time unit or precision", 2,
      "3.14.3"));
}

TEST(DesignBuildingBlockParsing, StepRejectedInCuScopeTimeunit) {
  auto r = PreprocessAndParse(
      "timeunit 1step;\n"
      "module m; endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "step cannot be used to set or modify the time unit or precision", 1,
      "3.14.3"));
}

// The precision-argument source (ii) must be picked up from a timeunit slash
// form living in an interface, not only in a module. Distinct production path
// from InterfacesAndProgramsContribute, which supplies a standalone
// timeprecision statement.
TEST(DesignBuildingBlockParsing, InterfaceTimeunitPrecArgContributes) {
  auto r = PreprocessAndParse(
      "interface i;\n"
      "  timeunit 1us / 1fs;\n"
      "endinterface\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

// Source (ii) contributed from the compilation-unit scope: a timeunit slash
// form outside all design elements sets the CU-scope precision, which the
// design-wide minimum must include. Distinct from CUScopeTimeprecisionIncluded,
// which uses a standalone timeprecision statement.
TEST(DesignBuildingBlockParsing, CuScopeTimeunitPrecArgContributes) {
  auto r = PreprocessAndParse(
      "timeunit 1us / 1fs;\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

// Source (i), a timeprecision statement, must be gathered from a module nested
// inside another module, exercising the recursive descent in the collector.
// The finer inner precision wins the design-wide minimum.
TEST(DesignBuildingBlockParsing, NestedModuleTimeprecisionContributes) {
  auto r = PreprocessAndParse(
      "module outer;\n"
      "  timeprecision 1ns;\n"
      "  module inner;\n"
      "    timeprecision 1ps;\n"
      "  endmodule\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

// Source (ii) contributed from a program's timeunit slash form, with the
// program supplying the unique design-wide minimum. Exercises the program
// syntactic position and the dedicated program collection loop, which no other
// test drives to the winning value (elsewhere an interface or module wins).
TEST(DesignBuildingBlockParsing, ProgramTimeunitPrecArgIsMinimum) {
  auto r = PreprocessAndParse(
      "interface i;\n"
      "  timeprecision 1ns;\n"
      "endinterface\n"
      "program p;\n"
      "  timeunit 1us / 1ps;\n"
      "endprogram\n"
      "module m;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

}  // namespace
