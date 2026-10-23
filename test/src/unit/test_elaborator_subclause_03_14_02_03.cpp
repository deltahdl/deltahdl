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
  // As the driver does, so each element takes the `timescale before it.
  ApplyModuleDirectives(cu, preproc.ModuleDirectivesList());
  cu->preproc_timescale = preproc.CurrentTimescale();
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
  // ValidateTimescaleConsistency scans modules before interfaces, so the
  // report stands at the unspecified module on line 5, not at the interface.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

// A program is one of the design-element kinds the consistency rule ranges
// over: a fully specified program alongside an unspecified module must be
// diagnosed just as a mixed pair of modules would be.
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
  // Modules are scanned before programs, so the unspecified module on line 5
  // is where the report stands.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

// §3.2 (printed page 50) counts a package among the design elements, and
// §3.14.2.2 lets a package declare its time unit and precision, so a fully
// specified package beside a module that specifies neither is the mix
// §3.14.2.3 forbids. Packages are scanned after modules, so the report stands
// at the unspecified module on line 5.
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

// The other way round: a fully specified module beside a package that
// specifies neither, reported at the package on line 5.
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

// An extern module declaration (§23.5) declares the ports of the module its
// definition gives and is no design element of its own, so it is not an
// unspecified element beside a definition that specifies both.
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

// Nor is it held to §3.14 on the values it would resolve to: here the
// compilation unit's lone 1 ps unit and the 1 ns default precision, which the
// definition replaces with its own 1 ps.
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

// §3.14.2.3 b): a package that declares only its unit takes its precision from
// the `timescale before it, 1 ps here, equal to its unit. The later 1 ns
// `timescale governs the module and not the package, so the design is legal
// and is not judged by the last directive of the compilation unit.
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

// A package that declares both of its own needs no `timescale, so a
// `timescale elsewhere in the compilation unit does not excuse it from §3.14:
// its 1 ns precision is coarser than its 1 ps unit.
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

// §3.14.2.3 b) ranks the `timescale before the package above the compilation
// unit's `timeunit 1ps;`, so the package runs at 1 ns / 1 ps and is legal.
// Resolved without the directive it would take the 1 ps unit and the 1 ns
// default precision, which is the false report the package is spared.
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

// §3.14.2.3 b): a package that declares only its unit takes the precision of
// the `timescale before it, 1 ns here, coarser than its 1 ps unit, which §3.14
// makes an error. The package was skipped and the design accepted.
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

// Packages and modules have name spaces of their own (§3.13), so a package and
// a module may share a name, and each takes the `timescale before its own
// header: the package 1 ns / 1 ns under its 1 ns unit, the module 1 ps / 1 ps
// under its 1 ps unit, both legal. Given the package's directive, the module
// would run at a 1 ns precision under its 1 ps unit and be rejected.
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

// §3.14.2.3 b) takes the `timescale that precedes an element, so a package
// before the compilation unit's only `timescale specifies neither value, while
// the module after it specifies both: the mix the clause forbids, reported at
// the package. It was counted as specified because a `timescale stood anywhere.
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

// The same of a module: one before the only `timescale is unspecified beside
// one after it.
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

// A package that declares both of its own is specified whatever header record
// the preprocessor kept for it, and it keeps none for a header after an
// attribute instance (#4892), so this one is judged by its own 1 ns / 1 ps.
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

// "Specified" means both a time unit and a time precision are in effect. An
// element carrying only a timeunit is still unspecified, so pairing it with a
// fully specified element trips the same error as pairing with a bare element.
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

// The other half of the same partial-specification form: an element that names
// only a time precision (and no time unit) is likewise not fully specified, so
// mixing it with a fully specified element is an error too.
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

// The cases below read the time scale the elaborator gave each element, which
// is what its delays are scaled by, rather than asking whether the design was
// accepted. Each source keeps every element's precision no coarser than its
// unit, so §3.14 rejects none of them.

// §3.14.2.3: an element's own timeunit stands ahead of the `timescale before
// it, which still supplies the precision the element omits.
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

// §3.14.2.3 a): a nested module that declares neither takes both from the
// module enclosing it.
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

// The same of an interface nested in an interface. The module instantiating
// the outer one declares a time scale of its own, which the inner interface
// does not take, since it is nested in the interface and not in the module.
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

// §3.14.2.3 b): an element that declares neither and is nested in nothing
// takes both from the last `timescale before it.
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

// §3.14.2.3 c): with no `timescale before it, the compilation unit's own
// declarations give both.
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

// §3.14.2.3 d): with nothing declared anywhere, the default, which deltahdl
// takes as 1 ns for both.
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

// Every source at once: the inner module's own 10 ns unit stands ahead of all
// of them, and the 100 ps precision it omits comes from the module enclosing
// it, ahead of the `timescale's 1 us and the compilation unit's 1 ps.
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

// §3.14.2.3 b) ranks the `timescale ahead of the compilation unit's timeunit,
// whichever of the two is written first.
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

// A precision the element omits follows the same order as a unit: the inner
// module declares only its unit and takes the outer module's 1 ps precision.
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

// The compilation unit's declarations reach an interface as they reach a
// module.
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

// And a program, here standing alone as its own top (§24.3).
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

// A program is never nested (§3.14.2.3 a), so one that declares neither, with
// no `timescale and no compilation-unit declaration, takes the default.
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

// Each element resolves on its own: under one `timescale, module a's own
// timeunit is a's alone, and module b takes the directive's unit. Both are
// elaborated as tops, so each is reached.
TEST(TimescalePrecedenceElaboration, IndependentResolution) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1us / 1ps\n"
      "module a;\n"
      "  timeunit 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
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

// A nested module that declares both of its own takes nothing from the module
// enclosing it.
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
