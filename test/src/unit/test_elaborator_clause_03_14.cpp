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

}  // namespace
