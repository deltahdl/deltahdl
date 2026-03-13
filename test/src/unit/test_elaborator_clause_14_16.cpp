#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SyncDriveElab, SimpleClockingDriveElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= 8'hFF;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, DriveWithCycleDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= ##2 8'hFF;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, InoutClockvarDriveElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial cb.data <= 8'hAB;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, ContinuousAssignToClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  assign data = 8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(SyncDriveElab, MultipleDrivesToSameOutputElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output nibble;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.nibble <= 4'b0101;\n"
             "    cb.nibble <= 4'b0011;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, WriteToInputClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial cb.data <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
