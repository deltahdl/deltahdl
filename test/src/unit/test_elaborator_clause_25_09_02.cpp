#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceModportClockingElaboration,
     DriveClockingOutputViaModportSelectedVif_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  task drive(virtual A_Bus.STB s);\n"
      "    s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     ReadClockingInputViaModportSelectedVif_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire gnt;\n"
      "  clocking sb @(posedge clk); input gnt; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  logic observed;\n"
      "  task sample_gnt(virtual A_Bus.STB s);\n"
      "    observed = s.sb.gnt;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     TypedefVirtualInterfaceWithModportAccessesClockingSignal_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "typedef virtual A_Bus.STB SYNCTB;\n"
      "module top;\n"
      "  task request(SYNCTB s);\n"
      "    s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     ClockingBlockNotListedInSelectedModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport TB(input gnt, output req);\n"
      "endinterface\n"
      "module top;\n"
      "  task drive(virtual A_Bus.TB s);\n"
      "    s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     ClockingInDifferentModportNotAccessibleThroughSelectedModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "  modport TB(input gnt, output req);\n"
      "endinterface\n"
      "module top;\n"
      "  task drive(virtual A_Bus.TB s);\n"
      "    s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     UnknownClockingNameThroughModportSelectedVif_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  task drive(virtual A_Bus.STB s);\n"
      "    s.nosuch.req <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingElaboration,
     UnknownSignalInSelectedModportClocking_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  wire req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  task drive(virtual A_Bus.STB s);\n"
      "    s.sb.missing <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
