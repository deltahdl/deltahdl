#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceModportClockingSim,
     LoweringSucceedsForModportSelectedVifWithClockingInModport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  clocking sb @(posedge clk); input gnt; output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "typedef virtual A_Bus.STB SYNCTB;\n"
      "module top;\n"
      "  logic clk;\n"
      "  A_Bus u(clk);\n"
      "  SYNCTB v;\n"
      "  initial v = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceModportClockingSim,
     DriveClockingOutputViaModportSelectedVifDrivesUnderlyingSignal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  logic req;\n"
      "  clocking sb @(posedge clk); output req; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  A_Bus u(clk);\n"
      "  virtual A_Bus.STB v;\n"
      "  task do_drive(virtual A_Bus.STB h); h.sb.req <= 1; endtask\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    u.req = 0;\n"
      "    v = u;\n"
      "    @(posedge clk);\n"
      "    do_drive(v);\n"
      "    @(posedge clk);\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #10 clk = 0;\n"
      "    #15 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* signal = f.ctx.FindVariable("top.u.req");
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(signal->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceModportClockingSim,
     ReadClockingInputViaModportSelectedVifReturnsSampledValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface A_Bus(input logic clk);\n"
      "  logic gnt;\n"
      "  clocking sb @(posedge clk); input gnt; endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  A_Bus u(clk);\n"
      "  virtual A_Bus.STB v;\n"
      "  logic observed;\n"
      "  task do_read(virtual A_Bus.STB h); observed = h.sb.gnt; endtask\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    u.gnt = 1;\n"
      "    v = u;\n"
      "    @(posedge clk);\n"
      "    do_read(v);\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* observed = f.ctx.FindVariable("top.observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 1u);
}

}  // namespace
