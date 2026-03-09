#include "fixture_elaborator.h"

namespace {

TEST(ElabClause03, Cl3_14_PrecisionLessPreciseThanUnit) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  timeunit 1ps;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_14_PrecisionEqualToUnit) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ns;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_14_PrecisionFinerThanUnit) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_14_NoTimescaleElaboratesOk) {
  EXPECT_TRUE(ElabOk("module m; logic x; endmodule\n"));
}

TEST(ElabClause03, Cl3_14_ModuleWithDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "  logic y;\n"
             "  assign #5 y = 1'b1;\n"
             "endmodule\n"));
}

}  // namespace
