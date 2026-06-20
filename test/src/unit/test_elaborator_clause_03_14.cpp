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

TEST(DesignBuildingBlockElaboration, ModuleWithDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "  logic y;\n"
             "  assign #5 y = 1'b1;\n"
             "endmodule\n"));
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

}  // namespace
