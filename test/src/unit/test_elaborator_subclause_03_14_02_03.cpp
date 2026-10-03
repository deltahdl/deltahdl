#include <gtest/gtest.h>

#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

static RtlirDesign* ElaborateWithPreprocAndCu(const std::string& src,
                                              ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  cu->preproc_timescale = preproc.CurrentTimescale();
  cu->has_preproc_timescale = preproc.HasTimescale();
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

}  // namespace
