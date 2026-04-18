#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceModportClockingParsing,
     TypedefVirtualInterfaceWithModportSelector) {
  EXPECT_TRUE(ParseOk(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module m;\n"
      "  typedef virtual A_Bus.STB SYNCTB;\n"
      "  SYNCTB v;\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceModportClockingParsing,
     DriveClockingOutputThroughModportSelectedVifInTask) {
  EXPECT_TRUE(ParseOk(
      "interface A_Bus(input logic clk);\n"
      "  wire req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module m;\n"
      "  typedef virtual A_Bus.STB SYNCTB;\n"
      "  task request(SYNCTB s);\n"
      "    s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceModportClockingParsing,
     WaitOnClockingInputThroughModportSelectedVif) {
  EXPECT_TRUE(ParseOk(
      "interface A_Bus(input logic clk);\n"
      "  wire gnt;\n"
      "  clocking sb @(posedge clk); input gnt; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module m;\n"
      "  typedef virtual A_Bus.STB SYNCTB;\n"
      "  task wait_grant(SYNCTB s);\n"
      "    wait(s.sb.gnt == 1);\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceModportClockingParsing,
     InlineVirtualInterfaceArgumentWithModportSelector) {
  EXPECT_TRUE(ParseOk(
      "interface A_Bus(input logic clk);\n"
      "  wire req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module m;\n"
      "  task drive(virtual A_Bus.STB h);\n"
      "    h.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceModportClockingParsing,
     ClockingMemberReadAndWriteMixedInSingleTask) {
  EXPECT_TRUE(ParseOk(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module m;\n"
      "  typedef virtual A_Bus.STB SYNCTB;\n"
      "  task handshake(SYNCTB s);\n"
      "    if (s.sb.gnt == 0)\n"
      "      s.sb.req <= 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

}  // namespace
