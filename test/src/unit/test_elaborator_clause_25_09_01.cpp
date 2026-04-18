#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceClockingElaboration, ReadClockingInputViaVif_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire a;\n"
      "  clocking sb @(posedge clk); input a; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic x;\n"
      "  task t(virtual SyncBus v); x = v.sb.a; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration, WriteClockingOutputViaVif_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire b;\n"
      "  clocking sb @(posedge clk); output b; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  task t(virtual SyncBus v); v.sb.b <= 0; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     WriteClockingInoutViaVifWithCycleDelay_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire c;\n"
      "  clocking sb @(posedge clk); inout c; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  task t(virtual SyncBus v); v.sb.c <= ##1 1; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration, TypedefVirtualInterfaceBoundToInstance_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u(clk);\n"
      "  VI v;\n"
      "  initial v = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     TaskParameterOfTypedefVirtualInterface_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire a, b, c;\n"
      "  clocking sb @(posedge clk);\n"
      "    input a; output b; inout c;\n"
      "  endclocking\n"
      "endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  task do_it(VI v);\n"
      "    if (v.sb.a == 1) v.sb.b <= 0;\n"
      "    else v.sb.c <= ##1 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     ArrayOfVifInitializedFromInterfaceInstances_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus b1(clk), b2(clk);\n"
      "  initial begin\n"
      "    VI v[2] = '{ b1, b2 };\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     UnknownClockingBlockNameThroughVif_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire a;\n"
      "  clocking sb @(posedge clk); input a; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic x;\n"
      "  task t(virtual SyncBus v); x = v.nosuch.a; endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     UnknownSignalInClockingBlockThroughVif_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  wire a;\n"
      "  clocking sb @(posedge clk); input a; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic x;\n"
      "  task t(virtual SyncBus v); x = v.sb.missing; endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     ArrayOfVifInitWithMismatchedInterfaceType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface SyncBus(input logic clk); endinterface\n"
      "interface OtherBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus b1(clk);\n"
      "  OtherBus b2(clk);\n"
      "  initial begin\n"
      "    VI v[2] = '{ b1, b2 };\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingElaboration,
     ArrayOfVifInitWithWrongElementCount_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface SyncBus(input logic clk); endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus b1(clk), b2(clk), b3(clk);\n"
      "  initial begin\n"
      "    VI v[2] = '{ b1, b2, b3 };\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
