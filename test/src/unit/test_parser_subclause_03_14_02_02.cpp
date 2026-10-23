#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_reported_error.h"
#include "parser/time_resolve.h"

using namespace delta;
namespace {

TEST(DesignBuildingBlockParsing, SingleModuleTimeunitSlash) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1us / 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_global_precision,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, KeywordsSetUnitAndPrecision) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, TimeunitSlashCombinesBoth) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, TimeunitAllSixUnits) {
  auto r_s = PreprocessAndParse("module m; timeunit 1s; endmodule\n");
  EXPECT_EQ(r_s.cu->modules[0]->time_unit, TimeUnit::kS);
  auto r_ms = PreprocessAndParse("module m; timeunit 1ms; endmodule\n");
  EXPECT_EQ(r_ms.cu->modules[0]->time_unit, TimeUnit::kMs);
  auto r_us = PreprocessAndParse("module m; timeunit 1us; endmodule\n");
  EXPECT_EQ(r_us.cu->modules[0]->time_unit, TimeUnit::kUs);
  auto r_ns = PreprocessAndParse("module m; timeunit 1ns; endmodule\n");
  EXPECT_EQ(r_ns.cu->modules[0]->time_unit, TimeUnit::kNs);
  auto r_ps = PreprocessAndParse("module m; timeunit 1ps; endmodule\n");
  EXPECT_EQ(r_ps.cu->modules[0]->time_unit, TimeUnit::kPs);
  auto r_fs = PreprocessAndParse("module m; timeunit 1fs; endmodule\n");
  EXPECT_EQ(r_fs.cu->modules[0]->time_unit, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, TimeunitSetsUnit) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, TimeprecisionSetsPrecision) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, SeparateDeclsWithMixedUnits) {
  auto r = PreprocessAndParse(
      "module D;\n"
      "  timeunit 100ps;\n"
      "  timeprecision 10fs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kPs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, SlashDeclWithMixedUnits) {
  auto r = PreprocessAndParse(
      "module E;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kPs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, RemovesFileOrderDependency) {
  auto r1 = PreprocessAndParse(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  auto r2 = PreprocessAndParse(
      "`timescale 1ms / 1us\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  EXPECT_EQ(r1.cu->modules[0]->time_unit, r2.cu->modules[0]->time_unit);
  EXPECT_EQ(r1.cu->modules[0]->time_prec, r2.cu->modules[0]->time_prec);
  EXPECT_EQ(r1.cu->modules[0]->time_unit, TimeUnit::kPs);
  EXPECT_EQ(r1.cu->modules[0]->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, WorksInInterface) {
  auto r = PreprocessAndParse(
      "interface ifc;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_TRUE(ifc->has_timeunit);
  EXPECT_TRUE(ifc->has_timeprecision);
  EXPECT_EQ(ifc->time_unit, TimeUnit::kUs);
  EXPECT_EQ(ifc->time_prec, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, WorksInProgram) {
  auto r = PreprocessAndParse(
      "program p;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 100ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* prog = r.cu->programs[0];
  EXPECT_TRUE(prog->has_timeunit);
  EXPECT_TRUE(prog->has_timeprecision);
  EXPECT_EQ(prog->time_unit, TimeUnit::kNs);
  EXPECT_EQ(prog->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, AllThreeMagnitudes) {
  EXPECT_FALSE(
      PreprocessAndParse("module m; timeunit 1ns; endmodule").has_errors);
  EXPECT_FALSE(
      PreprocessAndParse("module m; timeunit 10ns; endmodule").has_errors);
  EXPECT_FALSE(
      PreprocessAndParse("module m; timeunit 100ns; endmodule").has_errors);

  EXPECT_FALSE(
      PreprocessAndParse("module m; timeprecision 1ps; endmodule").has_errors);
  EXPECT_FALSE(
      PreprocessAndParse("module m; timeprecision 10ps; endmodule").has_errors);
  EXPECT_FALSE(PreprocessAndParse("module m; timeprecision 100ps; endmodule")
                   .has_errors);
}

TEST(DesignBuildingBlockParsing, TimeunitAloneNoPrec) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, TimeprecisionAloneNoUnit) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, PrecedeOtherItems) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  logic x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, RepeatMatchingDeclaration) {
  auto r = PreprocessAndParse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
  EXPECT_EQ(r.cu->modules[0]->time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->modules[0]->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, SeparateModulesIndependentScope) {
  auto r = PreprocessAndParse(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->modules[0]->time_prec, TimeUnit::kPs);
  EXPECT_EQ(r.cu->modules[1]->time_unit, TimeUnit::kUs);
  EXPECT_EQ(r.cu->modules[1]->time_prec, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, CUTimeunitSlashSyntax) {
  auto r = PreprocessAndParse(
      "timeunit 100ps / 10fs;\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kPs);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kFs);
}

TEST(CompilationUnitStructure, TimeunitDeclarationSetsFlag) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
}

TEST(CompilationUnitStructure, TimeprecisionDeclarationSetsFlag) {
  auto r = Parse(
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(CompilationUnitTimeDeclarations, TimeunitAndTimeprecisionBothSet) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSameModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 1us;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeprecisionInSameModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  logic x;\n"
      "  timeprecision 10fs;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision does not match prior declaration", 5,
                            "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, TimeunitAfterOtherItemsWithoutPriorRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing,
     TimeprecisionAfterOtherItemsWithoutPriorRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing,
     TimeunitMatchingRepeatAfterOtherItemsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  timeunit 1ns;\n"
              "  logic x;\n"
              "  timeunit 1ns;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing,
     DistinctTimeunitMagnitudeInSameModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 10ns;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSameInterfaceRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 1us;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSameProgramRejected) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 1us;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(CompilationUnitTimeDeclarations, DistinctTimeunitInCuRejected) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "module m; endmodule\n"
      "timeunit 1us;\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 3, "3.14.2.2"));
}

TEST(CompilationUnitTimeDeclarations, DistinctTimeprecisionInCuRejected) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module m; endmodule\n"
      "timeprecision 10fs;\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision does not match prior declaration", 4,
                            "3.14.2.2"));
}

TEST(CompilationUnitTimeDeclarations,
     TimeunitAfterModuleWithoutPriorInCuRejected) {
  auto r = Parse(
      "module m; endmodule\n"
      "timeunit 1ns;\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            2, "3.14.2.2"));
}

TEST(CompilationUnitTimeDeclarations, TimeunitMatchingRepeatAfterModuleInCu) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "module m; endmodule\n"
      "timeunit 1ns;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, TimeunitInPackageStored) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(r.cu->packages[0]->has_timeunit);
  EXPECT_TRUE(r.cu->packages[0]->has_timeprecision);
  EXPECT_EQ(r.cu->packages[0]->time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->packages[0]->time_prec, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSamePackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  parameter int x = 1;\n"
      "  timeunit 1us;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeprecisionInSamePackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  parameter int x = 1;\n"
      "  timeprecision 10fs;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision does not match prior declaration", 5,
                            "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing,
     TimeunitAfterOtherItemsWithoutPriorInPackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  parameter int x = 1;\n"
      "  timeunit 1ns;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, TimeunitMatchingRepeatInPackageAccepted) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  parameter int x = 1;\n"
      "  timeunit 1ns;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->packages[0]->has_timeunit);
  EXPECT_EQ(r.cu->packages[0]->time_unit, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing,
     TimeunitAfterOtherItemsWithoutPriorInInterfaceRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing,
     TimeunitAfterOtherItemsWithoutPriorInProgramRejected) {
  auto r = Parse(
      "program p;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, TimeunitMatchingRepeatInInterfaceAccepted) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->interfaces[0]->has_timeunit);
  EXPECT_EQ(r.cu->interfaces[0]->time_unit, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, TimeunitMatchingRepeatInProgramAccepted) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->programs[0]->has_timeunit);
  EXPECT_EQ(r.cu->programs[0]->time_unit, TimeUnit::kNs);
}

// The slash form of `timeunit` is admitted in every design-element scope, not
// only in modules and the compilation unit. These exercise it in an interface,
// a program, and a package so each syntactic position's combined unit/precision
// parse is observed; the package case drives the distinct code path that stores
// the slash-supplied precision onto the package declaration.
TEST(DesignBuildingBlockParsing, TimeunitSlashInInterfaceSetsBoth) {
  auto r = PreprocessAndParse(
      "interface ifc;\n"
      "  timeunit 100ps / 10fs;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_TRUE(ifc->has_timeunit);
  EXPECT_TRUE(ifc->has_timeprecision);
  EXPECT_EQ(ifc->time_unit, TimeUnit::kPs);
  EXPECT_EQ(ifc->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, TimeunitSlashInProgramSetsBoth) {
  auto r = PreprocessAndParse(
      "program p;\n"
      "  timeunit 100ps / 10fs;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* prog = r.cu->programs[0];
  EXPECT_TRUE(prog->has_timeunit);
  EXPECT_TRUE(prog->has_timeprecision);
  EXPECT_EQ(prog->time_unit, TimeUnit::kPs);
  EXPECT_EQ(prog->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, TimeunitSlashInPackageSetsBoth) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 100ps / 10fs;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  EXPECT_TRUE(pkg->has_timeunit);
  EXPECT_TRUE(pkg->has_timeprecision);
  EXPECT_EQ(pkg->time_unit, TimeUnit::kPs);
  EXPECT_EQ(pkg->time_prec, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, TimeunitInGenerateBlockRejected) {
  auto r = Parse(
      "module top;\n"
      "  if (1) begin : g\n"
      "    timeunit 10ns;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a timeunit or timeprecision declaration is not an "
                            "item of a generate block or region, which is no "
                            "time scope",
                            3, "3.14.2.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
}

TEST(DesignBuildingBlockParsing, TimeprecisionInGenerateRegionRejected) {
  auto r = Parse(
      "module top;\n"
      "  generate\n"
      "    timeprecision 1ps;\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a timeunit or timeprecision declaration is not an "
                            "item of a generate block or region, which is no "
                            "time scope",
                            3, "3.14.2.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, TimeunitAfterNonAnsiPortDeclRejected) {
  auto r = Parse(
      "module top(a);\n"
      "  input a;\n"
      "  timeunit 10ns;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(DesignBuildingBlockParsing, TimeunitBeforeNonAnsiPortDeclAccepted) {
  auto r = Parse(
      "module top(a);\n"
      "  timeunit 10ns;\n"
      "  input a;\n"
      "  timeunit 10ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_EQ(r.cu->modules[0]->time_unit_magnitude, 10);
}

// §3.14.2.2: the time scope's timeunit and timeprecision declarations precede
// every other item, A.10 footnote 3 making one written later legal only as a
// matching repeat. A null item, an anonymous program, a modport and a bind
// directive are items like any other, though none is kept in the body's item
// list, so a declaration after one is a later item (#7586).
TEST(DesignBuildingBlockParsing, TimeunitAfterAnUnlistedItemIsALaterItem) {
  auto r = Parse(
      "package p1;\n"
      "  ;\n"
      "  timeunit 1ns;\n"
      "endpackage\n"
      "package p2;\n"
      "  program;\n"
      "  endprogram\n"
      "  timeunit 1ns;\n"
      "endpackage\n"
      "module m1;\n"
      "  ;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "interface i1;\n"
      "  modport mp (input x);\n"
      "  timeunit 1ns;\n"
      "endinterface\n"
      "program pr1;\n"
      "  ;\n"
      "  timeunit 1ns;\n"
      "endprogram\n"
      "module m2;\n"
      "  bind m1 m3 u ();\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  const char* const kUnit =
      "timeunit as a later item requires a matching prior declaration in the "
      "same time scope";
  EXPECT_TRUE(ReportedError(r.diags, kUnit, 3, "3.14.2.2"));
  EXPECT_TRUE(ReportedError(r.diags, kUnit, 8, "3.14.2.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision as a later item requires a matching "
                            "prior declaration in the same time scope",
                            12, "3.14.2.2"));
  EXPECT_TRUE(ReportedError(r.diags, kUnit, 16, "3.14.2.2"));
  EXPECT_TRUE(ReportedError(r.diags, kUnit, 20, "3.14.2.2"));
  EXPECT_TRUE(ReportedError(r.diags, kUnit, 24, "3.14.2.2"));
}

// The declaration that opens the body is the scope's first, and a null item
// after it leaves a matching repeat legal (#7586).
TEST(DesignBuildingBlockParsing, TimeunitBeforeANullItemIsTheFirst) {
  auto r = Parse(
      "timeunit 1ns;\n"
      ";\n"
      "timeunit 1ns;\n"
      "package p;\n"
      "  timeunit 1ns;\n"
      "  ;\n"
      "  timeunit 1ns;\n"
      "endpackage\n"
      "interface i;\n"
      "  timeunit 1ns;\n"
      "  modport mp (input x);\n"
      "endinterface\n"
      "module m;\n"
      "  timeprecision 1ps;\n"
      "  ;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// The compilation-unit scope is a time scope of its own, and the null item and
// a bind directive written in it are items that leave none of its lists longer
// (#7586).
TEST(DesignBuildingBlockParsing, TimeunitAfterAnUnlistedCuItemIsALaterItem) {
  const char* const kUnit =
      "timeunit as a later item requires a matching prior declaration in the "
      "same time scope";
  auto after_null = Parse(
      ";\n"
      "timeunit 1ns;\n");
  EXPECT_TRUE(ReportedError(after_null.diags, kUnit, 2, "3.14.2.2"));
  auto after_bind = Parse(
      "bind m1 m3 u ();\n"
      "timeunit 1ns;\n");
  EXPECT_TRUE(ReportedError(after_bind.diags, kUnit, 2, "3.14.2.2"));
}

}  // namespace
