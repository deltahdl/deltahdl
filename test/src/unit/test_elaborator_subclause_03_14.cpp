#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// Every report named below stands on the line of its design element's keyword
// because CheckTimescaleOrder in
// src/elaborator/elaborator_validate_timescale.cpp anchors the
// precision-no-coarser-than-unit report on the design element's range.start,
// which is the module/package/interface/program keyword, and not on the
// declaration that broke the rule. The precision and the unit it compares may
// each have come from somewhere other than the element.
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

// The precision-no-coarser-than-unit rule names a design element, which
// includes packages. A package is not elaborated through the module item path,
// so the separate-statement form of the check must be applied to packages in
// their own right. Each package is paired with a top module that specifies its
// own time unit and precision, as the package does, so that §3.14.2.3's rule
// against mixing specified and unspecified design elements is met and the only
// thing that can make elaboration fail is the package's timescale.
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

// The rule likewise governs interfaces and programs. An interface or program
// that is never instantiated is not reached through module item elaboration, so
// the separate-statement form of the check must be applied to its declaration.
// Every design element here is fully specified so the §3.14.2.3 "all or none"
// consistency rule does not mask the precision check under test.
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

// §3.14.2.3 (printed page 60) gives a design element that declares no
// timeprecision the precision the same precedence gives a time unit: the
// enclosing module, then the last `timescale, then the compilation unit, and
// otherwise the default, which deltahdl takes as 1 ns. §3.14 (printed 59) holds
// the element to the precision so resolved. A module whose only time
// declaration is `timeunit 1ns;` therefore runs at the 1 ns default, equal to
// its unit, and elaborates cleanly.
TEST(DesignBuildingBlockElaboration, LoneTimeunitEqualToDefaultPrecision) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

// The same module with `timeunit 1ps;` runs at the 1 ns default precision too,
// which is coarser than its unit, so it is rejected; accepted, its #1500 ran
// as a 1 ns delay.
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

// A lone timeprecision takes its unit by the same precedence: under the 1 ns
// default unit, `timeprecision 10ns;` is coarser than the unit.
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

// §3.14.2.3 b): the `timescale in force at the header gives the precision a
// module does not declare. Its 1 ps precision matches the module's own 1 ps
// unit, so the module is accepted where the 1 ns default would have been
// coarser than it.
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

// The `timescale precision can be the coarser one: 10 ps under a module's
// own 1 ps unit.
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

// §3.14.2.3 c): the compilation unit's timeunit gives the unit a module does
// not declare, so a module declaring only `timeprecision 1ns;` under a unit of
// `timeunit 1ps;` has a precision coarser than its unit. The compilation unit
// declares its precision too, so that only the module's own pair is in breach.
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

// A module that declares neither is held to the rule all the same when its two
// values come from different places: here its unit is the compilation unit's
// 1 ps and its precision the 1 ns default.
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

// The compilation unit's own pair, declared as two statements, reaches the
// module that declares neither: §3.14.2.3 c) gives it both, and §3.14 holds
// the module to them.
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

// §3.14.2.3 a): a nested module inherits what it does not declare from the
// module enclosing it, ahead of the `timescale, the compilation unit and the
// default. The inner module's lone `timeunit 1ps;` takes the outer 1 ps
// precision and is accepted where the 1 ns default would have rejected it.
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

// The inherited precision can be the coarser one: the outer 10 ps under the
// inner module's own 1 ps unit, reported at the inner module.
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

// The other half of §3.14.2.3 a): an inner module that declares only its
// precision takes the outer 1 ns unit, and its own 10 ns precision is coarser
// than that inherited unit, so the pair is the inner module's and is reported
// there rather than passed over as inherited.
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

// A package is a design element (§3.2, printed 50) and resolves what it does
// not declare by the same precedence, less the enclosing module it cannot
// have: its lone `timeunit 1ps;` runs at the 1 ns default precision.
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
