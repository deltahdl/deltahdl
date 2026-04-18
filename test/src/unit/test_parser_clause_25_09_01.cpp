#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceClockingParsing, ClockingMemberAccessViaVifInTask) {
  auto r = Parse(
      "interface SyncBus(input logic clk);\n"
      "  wire a, b, c;\n"
      "  clocking sb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "    inout c;\n"
      "  endclocking\n"
      "endinterface\n"
      "module m;\n"
      "  task do_it(virtual SyncBus v);\n"
      "    if (v.sb.a == 1)\n"
      "      v.sb.b <= 0;\n"
      "    else\n"
      "      v.sb.c <= ##1 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualInterfaceClockingParsing, TypedefVirtualInterfaceType) {
  auto r = Parse(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module m;\n"
      "  VI v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualInterfaceClockingParsing, NonBlockingAssignToClockingOutputViaVif) {
  EXPECT_TRUE(ParseOk(
      "interface SyncBus(input logic clk);\n"
      "  wire b;\n"
      "  clocking sb @(posedge clk); output b; endclocking\n"
      "endinterface\n"
      "module m;\n"
      "  task t(virtual SyncBus v);\n"
      "    v.sb.b <= 0;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceClockingParsing,
     IntraAssignmentCycleDelayToClockingInoutViaVif) {
  EXPECT_TRUE(ParseOk(
      "interface SyncBus(input logic clk);\n"
      "  wire c;\n"
      "  clocking sb @(posedge clk); inout c; endclocking\n"
      "endinterface\n"
      "module m;\n"
      "  task t(virtual SyncBus v);\n"
      "    v.sb.c <= ##1 1;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceClockingParsing, ReadClockingInputViaVifInExpression) {
  EXPECT_TRUE(ParseOk(
      "interface SyncBus(input logic clk);\n"
      "  wire a;\n"
      "  clocking sb @(posedge clk); input a; endclocking\n"
      "endinterface\n"
      "module m;\n"
      "  logic r;\n"
      "  task t(virtual SyncBus v);\n"
      "    r = v.sb.a;\n"
      "  endtask\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceClockingParsing,
     ArrayOfVirtualInterfaceInitializedByAssignmentPattern) {
  EXPECT_TRUE(ParseOk(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus b1(clk), b2(clk);\n"
      "  initial begin\n"
      "    VI v[2] = '{ b1, b2 };\n"
      "  end\n"
      "endmodule\n"));
}

TEST(VirtualInterfaceClockingParsing,
     ArrayOfVirtualInterfaceIndexedInTaskCall) {
  EXPECT_TRUE(ParseOk(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus b1(clk), b2(clk);\n"
      "  task do_it(VI v); endtask\n"
      "  initial begin\n"
      "    VI v[2] = '{ b1, b2 };\n"
      "    do_it(v[0]);\n"
      "    do_it(v[1]);\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
