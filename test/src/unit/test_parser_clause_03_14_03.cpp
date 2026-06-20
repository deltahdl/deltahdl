#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"
#include "parser/time_resolve.h"

using namespace delta;
namespace {

TEST(DesignBuildingBlockParsing, ConsidersTimescalePrec) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, MinAcrossAllThreeSources) {
  auto r = ParseTimescale31402(
      "`timescale 1us / 1ns\n"
      "module a;\n"
      "  timeunit 1ms / 1us;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, DefaultWhenNoneSpecified) {
  auto r = ParseTimescale31402(
      "module a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, CUScopeTimeprecisionIncluded) {
  auto r = ParseTimescale31402(
      "timeprecision 1fs;\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, InterfacesAndProgramsContribute) {
  auto r = ParseTimescale31402(
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
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, MinOfTimeprecisionStatements) {
  auto r = ParseTimescale31402(
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
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, ConsidersTimeunitPrecArg) {
  auto r = ParseTimescale31402(
      "module a;\n"
      "  timeunit 1us / 1fs;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, PackageTimeprecisionContributes) {
  auto r = ParseTimescale31402(
      "package p;\n"
      "  timeprecision 1fs;\n"
      "endpackage\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, PackageTimeunitPrecArgContributes) {
  auto r = ParseTimescale31402(
      "package p;\n"
      "  timeunit 1us / 1fs;\n"
      "endpackage\n"
      "module m;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeunit) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeprecision) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeprecision 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, StepRejectedAsTimeunitPrecArg) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns / 1step;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, TimeunitWithoutPrecArgDoesNotContribute) {
  auto r = ParseTimescale31402(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1fs;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, StepRejectedInPackageTimeunit) {
  auto r = ParseTimescale31402(
      "package p;\n"
      "  timeunit 1step;\n"
      "endpackage\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, StepRejectedInCuScopeTimeunit) {
  auto r = ParseTimescale31402(
      "timeunit 1step;\n"
      "module m; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
