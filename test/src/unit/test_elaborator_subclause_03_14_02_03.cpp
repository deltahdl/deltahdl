#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_design.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

static RtlirDesign* ElaborateWithPreprocAndCu(const std::string& src,
                                              ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  ApplyModuleDirectives(cu, preproc.ModuleDirectivesList());
  cu->has_preproc_global_precision = preproc.HasGlobalPrecision();
  cu->preproc_global_precision = preproc.GlobalPrecision();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

TEST(TimescalePrecedenceElaboration, MixedKeywordSpecificationErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, UniformKeywordsAcceptable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, UniformlyUnspecifiedAcceptable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PreprocTimescaleSuppliesFallback) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ps\n"
      "module a;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, CuTimeunitSuppliesFallback) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module a;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, MixedAcrossModuleAndInterfaceErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "interface bus_if;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n"
      "module a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, MixedAcrossProgramAndModuleErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "program p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n"
      "module a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, MixedAcrossPackageAndModuleErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n"
      "module a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, MixedAcrossModuleAndPackageErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "package p;\n"
      "endpackage\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, ExternDeclarationIsNotAnElement) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "extern module m;\n"
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, ExternDeclarationIsNotOrderChecked) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "timeunit 1ps;\n"
      "extern module m;\n"
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PackageFollowsTheTimescaleBeforeIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ps / 1ps\n"
      "package p;\n"
      "  timeunit 1ps;\n"
      "endpackage\n"
      "`timescale 1ns / 1ns\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PackageDeclaringBothIsOrderChecked) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ps\n"
      "package p;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1ns;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            2, "3.14"));
}

TEST(TimescalePrecedenceElaboration, PackageDeclaringNeitherFollowsTimescale) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ps\n"
      "timeunit 1ps;\n"
      "package p;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PackageTakesThePrecisionBeforeIt) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ns\n"
      "package p;\n"
      "  timeunit 1ps;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "time precision is less precise than the time unit",
                            2, "3.14"));
}

TEST(TimescalePrecedenceElaboration, PackageAndModuleOfOneNameTakeTheirOwn) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ns\n"
      "package m;\n"
      "  timeunit 1ns;\n"
      "endpackage\n"
      "`timescale 1ps / 1ps\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PackageBeforeEveryTimescaleIsUnspecified) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "package p;\n"
      "endpackage\n"
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            1, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, ModuleBeforeEveryTimescaleIsUnspecified) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "endmodule\n"
      "`timescale 1ns / 1ps\n"
      "module b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            1, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration,
     AttributedPackageDeclaringBothIsSpecified) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ps\n"
      "(* keep *) package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, UniformPackageAndModuleAcceptable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n"
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PartialSpecificationIsUnspecified) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1ns;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, PrecisionOnlyIsUnspecified) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

TEST(TimescalePrecedenceElaboration, ExplicitTimeunitTakesPriority) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1us / 1fs\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.magnitude, 1);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, ExplicitTimeprecisionTakesPriority) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(mod->timescale.magnitude, 1);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, NestedModuleInheritsEnclosingUnit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module outer;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "  module inner;\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* inner = FindModule(design, "inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(inner->timescale.magnitude, 1);
  EXPECT_EQ(inner->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(inner->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration,
     NestedInterfaceInheritsEnclosingTimescale) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "interface outer_if;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  interface inner_if;\n"
      "  endinterface\n"
      "  inner_if v();\n"
      "endinterface\n"
      "module m;\n"
      "  timeunit 1ms;\n"
      "  timeprecision 1ps;\n"
      "  outer_if u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* inner = FindModule(design, "inner_if");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(inner->timescale.magnitude, 1);
  EXPECT_EQ(inner->timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(inner->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, FallbackToPreviousTimescaleDirective) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(mod->timescale.magnitude, 1);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, FallbackToCompilationUnitTimeunit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "timeunit 10ps;\n"
      "timeprecision 1fs;\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.magnitude, 10);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, FallbackToDefaultWhenNothingSpecified) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(mod->timescale.magnitude, 1);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, FullPrecedenceChain) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ms / 1us\n"
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module outer;\n"
      "  timeunit 1us;\n"
      "  timeprecision 100ps;\n"
      "  module inner;\n"
      "    timeunit 10ns;\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* outer = FindModule(design, "outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(outer->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(outer->timescale.prec_magnitude, 100);
  const auto* inner = FindModule(design, "inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(inner->timescale.magnitude, 10);
  EXPECT_EQ(inner->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(inner->timescale.prec_magnitude, 100);
}

TEST(TimescalePrecedenceElaboration, TimescaleBeforeCUTimeunit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "timeunit 1fs;\n"
      "`timescale 100us / 10ps\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(mod->timescale.magnitude, 100);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 10);
}

TEST(TimescalePrecedenceElaboration, SameRulesForPrecision) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module outer;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  module inner;\n"
      "    timeunit 1ns;\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* inner = FindModule(design, "inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(inner->timescale.magnitude, 1);
  EXPECT_EQ(inner->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(inner->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, CUTimeunitAppliesToInterface) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "timeunit 1ps;\n"
      "timeprecision 1fs;\n"
      "interface i;\n"
      "endinterface\n"
      "module m;\n"
      "  i u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* iface = FindModule(design, "i");
  ASSERT_NE(iface, nullptr);
  EXPECT_EQ(iface->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(iface->timescale.magnitude, 1);
  EXPECT_EQ(iface->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(iface->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, CUTimeunitAppliesToProgram) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "timeunit 1us;\n"
      "timeprecision 10ns;\n"
      "program p;\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* prog = FindModule(design, "p");
  ASSERT_NE(prog, nullptr);
  EXPECT_EQ(prog->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(prog->timescale.magnitude, 1);
  EXPECT_EQ(prog->timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(prog->timescale.prec_magnitude, 10);
}

TEST(TimescalePrecedenceElaboration, ProgramDeclaringNothingTakesTheDefault) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "program p;\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* prog = FindModule(design, "p");
  ASSERT_NE(prog, nullptr);
  EXPECT_EQ(prog->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(prog->timescale.magnitude, 1);
  EXPECT_EQ(prog->timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(prog->timescale.prec_magnitude, 1);
}

TEST(TimescalePrecedenceElaboration, IndependentResolution) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1us / 1ps\n"
      "module a;\n"
      "  timeunit 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* a = FindModule(design, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(a->timescale.precision, TimeUnit::kPs);
  const auto* b = FindModule(design, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(b->timescale.precision, TimeUnit::kPs);
}

TEST(TimescalePrecedenceElaboration, NestedOverridesInheritance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module outer;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  module inner;\n"
      "    timeunit 1fs;\n"
      "    timeprecision 1fs;\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* inner = FindModule(design, "inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->timescale.unit, TimeUnit::kFs);
  EXPECT_EQ(inner->timescale.magnitude, 1);
  EXPECT_EQ(inner->timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(inner->timescale.prec_magnitude, 1);
}

}  // namespace
