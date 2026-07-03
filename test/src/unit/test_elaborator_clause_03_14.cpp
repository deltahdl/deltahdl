#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, PrecisionLessPreciseThanUnit) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 10ns;\n"
             "endmodule\n"));
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 10ps;\n"
             "  timeprecision 100ps;\n"
             "endmodule\n"));
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

// The precision-no-coarser-than-unit rule names "a design element", which
// includes packages. A package is not elaborated through the module item path,
// so the separate-statement form of the check must be applied to packages in
// their own right. Each package is paired with a trivial top module so that the
// only thing that can make elaboration fail is the package's timescale.
TEST(DesignBuildingBlockElaboration, PackagePrecisionLessPreciseThanUnit) {
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PackagePrecisionFinerThanUnitAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, PackagePrecisionEqualToUnitAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ns;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration,
     PackagePrecisionLongerByMagnitudeRejected) {
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 10ns;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

// The rule likewise governs interfaces and programs. An interface or program
// that is never instantiated is not reached through module item elaboration, so
// the separate-statement form of the check must be applied to its declaration.
// Every design element here is fully specified so the §3.14.2.3 "all or none"
// consistency rule does not mask the precision check under test.
TEST(DesignBuildingBlockElaboration, UninstantiatedInterfacePrecisionRejected) {
  EXPECT_FALSE(
      ElabOk("interface intf;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endinterface\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("program prog;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endprogram\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, UninstantiatedProgramPrecisionAccepted) {
  EXPECT_TRUE(
      ElabOk("program prog;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endprogram\n"
             "module m; timeunit 1ns; timeprecision 1ps; endmodule\n"));
}

// The comparison applies only when a design element supplies both a time unit
// and a time precision. A design element that names just one of the two has
// nothing to compare, so the check must not fire: here a module with only a
// time unit (no precision) elaborates cleanly.
TEST(DesignBuildingBlockElaboration, OnlyTimeUnitDoesNotTriggerPrecisionCheck) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

}  // namespace
