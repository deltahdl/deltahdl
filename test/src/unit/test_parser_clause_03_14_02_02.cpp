#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "parser/time_resolve.h"

using namespace delta;
namespace {

TEST(DesignBuildingBlockParsing, SingleModuleTimeunitSlash) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1us / 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, KeywordsSetUnitAndPrecision) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r_s = ParseTimescale31402("module m; timeunit 1s; endmodule\n");
  EXPECT_EQ(r_s.cu->modules[0]->time_unit, TimeUnit::kS);
  auto r_ms = ParseTimescale31402("module m; timeunit 1ms; endmodule\n");
  EXPECT_EQ(r_ms.cu->modules[0]->time_unit, TimeUnit::kMs);
  auto r_us = ParseTimescale31402("module m; timeunit 1us; endmodule\n");
  EXPECT_EQ(r_us.cu->modules[0]->time_unit, TimeUnit::kUs);
  auto r_ns = ParseTimescale31402("module m; timeunit 1ns; endmodule\n");
  EXPECT_EQ(r_ns.cu->modules[0]->time_unit, TimeUnit::kNs);
  auto r_ps = ParseTimescale31402("module m; timeunit 1ps; endmodule\n");
  EXPECT_EQ(r_ps.cu->modules[0]->time_unit, TimeUnit::kPs);
  auto r_fs = ParseTimescale31402("module m; timeunit 1fs; endmodule\n");
  EXPECT_EQ(r_fs.cu->modules[0]->time_unit, TimeUnit::kFs);
}

TEST(DesignBuildingBlockParsing, TimeunitSetsUnit) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r1 = ParseTimescale31402(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  auto r2 = ParseTimescale31402(
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

TEST(DesignBuildingBlockParsing, DefinesTimeScope) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, WorksInInterface) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
      ParseTimescale31402("module m; timeunit 1ns; endmodule").has_errors);
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeunit 10ns; endmodule").has_errors);
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeunit 100ns; endmodule").has_errors);

  EXPECT_FALSE(
      ParseTimescale31402("module m; timeprecision 1ps; endmodule").has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeprecision 10ps; endmodule")
                   .has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeprecision 100ps; endmodule")
                   .has_errors);
}

TEST(DesignBuildingBlockParsing, TimeunitAloneNoPrec) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, TimeprecisionAloneNoUnit) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, PrecedeOtherItems) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  timeunit 1ns;\n"
              "  logic x;\n"
              "  timeunit 1us;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeprecisionInSameModuleRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  timeunit 1ns;\n"
              "  timeprecision 1ps;\n"
              "  logic x;\n"
              "  timeprecision 10fs;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, TimeunitAfterOtherItemsWithoutPriorRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  logic x;\n"
              "  timeunit 1ns;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing,
     TimeprecisionAfterOtherItemsWithoutPriorRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  logic x;\n"
              "  timeprecision 1ps;\n"
              "endmodule\n"));
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
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  timeunit 1ns;\n"
              "  logic x;\n"
              "  timeunit 10ns;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSameInterfaceRejected) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  timeunit 1ns;\n"
              "  logic x;\n"
              "  timeunit 1us;\n"
              "endinterface\n"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeunitInSameProgramRejected) {
  EXPECT_FALSE(
      ParseOk("program p;\n"
              "  timeunit 1ns;\n"
              "  logic x;\n"
              "  timeunit 1us;\n"
              "endprogram\n"));
}

TEST(CompilationUnitTimeDeclarations, DistinctTimeunitInCuRejected) {
  EXPECT_FALSE(
      ParseOk("timeunit 1ns;\n"
              "module m; endmodule\n"
              "timeunit 1us;\n"));
}

TEST(CompilationUnitTimeDeclarations, DistinctTimeprecisionInCuRejected) {
  EXPECT_FALSE(
      ParseOk("timeunit 1ns;\n"
              "timeprecision 1ps;\n"
              "module m; endmodule\n"
              "timeprecision 10fs;\n"));
}

TEST(CompilationUnitTimeDeclarations,
     TimeunitAfterModuleWithoutPriorInCuRejected) {
  EXPECT_FALSE(
      ParseOk("module m; endmodule\n"
              "timeunit 1ns;\n"));
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
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  timeunit 1ns;\n"
              "  parameter int x = 1;\n"
              "  timeunit 1us;\n"
              "endpackage\n"));
}

TEST(DesignBuildingBlockParsing, DistinctTimeprecisionInSamePackageRejected) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  timeunit 1ns;\n"
              "  timeprecision 1ps;\n"
              "  parameter int x = 1;\n"
              "  timeprecision 10fs;\n"
              "endpackage\n"));
}

TEST(DesignBuildingBlockParsing,
     TimeunitAfterOtherItemsWithoutPriorInPackageRejected) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  parameter int x = 1;\n"
              "  timeunit 1ns;\n"
              "endpackage\n"));
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
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  logic x;\n"
              "  timeunit 1ns;\n"
              "endinterface\n"));
}

TEST(DesignBuildingBlockParsing,
     TimeunitAfterOtherItemsWithoutPriorInProgramRejected) {
  EXPECT_FALSE(
      ParseOk("program p;\n"
              "  logic x;\n"
              "  timeunit 1ns;\n"
              "endprogram\n"));
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

}  // namespace
