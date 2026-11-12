#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

template <typename Fixture>
void ProbeAt(Fixture& f, Variable* var, uint64_t time, uint64_t* dst) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [var, dst]() { *dst = var->value.ToUint64(); };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kPostponed, ev);
}

TEST(SyncDriveSignals, LastDriveInSameReNBAWinsAtClockingEvent) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  cmgr.RegisterEdgeCallback("pe", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

TEST(SyncDriveSignals, LastDriveInSameReNBAWinsBetweenClockingEvents) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{7}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

TEST(SyncDriveSignals, DrivesAtDifferentCyclesMatureIndependently) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  int events = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    ++events;
    if (events == 1)
      cmgr.ScheduleOutputDrive("cb", "v", 0xAA, f.ctx, f.scheduler);
    else if (events == 2)
      cmgr.ScheduleOutputDrive("cb", "v", 0xBB, f.ctx, f.scheduler);
  });

  uint64_t after_first = 0;
  uint64_t after_second = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 13, &after_first);
  ScheduleNegedge(f, clk, 16);
  SchedulePosedge(f, clk, 20);
  ProbeAt(f, v, 25, &after_second);
  f.scheduler.Run();

  EXPECT_EQ(after_first, 0xAAu);
  EXPECT_EQ(after_second, 0xBBu);
}

TEST(SyncDriveSignals, SharedOutputAcrossBlocksTakesMostRecentDrive) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* j = f.ctx.CreateVariable("j", 8);
  j->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;

  ClockingBlock pe;
  pe.name = "pe";
  pe.clock_signal = "clk";
  pe.clock_edge = Edge::kPosedge;
  ClockingSignal pe_sig;
  pe_sig.signal_name = "j";
  pe_sig.direction = ClockingDir::kOutput;
  pe.signals.push_back(pe_sig);
  cmgr.Register(pe);

  ClockingBlock ne;
  ne.name = "ne";
  ne.clock_signal = "clk";
  ne.clock_edge = Edge::kNegedge;
  ClockingSignal ne_sig;
  ne_sig.signal_name = "j";
  ne_sig.direction = ClockingDir::kOutput;
  ne.signals.push_back(ne_sig);
  cmgr.Register(ne);

  cmgr.Attach(f.ctx, f.scheduler);

  cmgr.RegisterEdgeCallback("pe", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("pe", "j", 0x11, f.ctx, f.scheduler);
  });
  cmgr.RegisterEdgeCallback("ne", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("ne", "j", 0x22, f.ctx, f.scheduler);
  });

  uint64_t after_posedge = 0;
  uint64_t after_negedge = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, j, 12, &after_posedge);
  ScheduleNegedge(f, clk, 15);
  ProbeAt(f, j, 18, &after_negedge);
  f.scheduler.Run();

  EXPECT_EQ(after_posedge, 0x11u);
  EXPECT_EQ(after_negedge, 0x22u);
}

TEST(SyncDriveSignals, ProceduralValueHeldUntilSynchronousDrive) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("cb", "v", 0x77, f.ctx, f.scheduler);
  });

  auto* proc = f.scheduler.GetEventPool().Acquire();
  proc->callback = [&]() { v->value = MakeLogic4VecVal(f.arena, 8, 0x33); };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, proc);

  uint64_t held = 0;
  uint64_t after_drive = 0;
  ProbeAt(f, v, 8, &held);
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 12, &after_drive);
  f.scheduler.Run();

  EXPECT_EQ(held, 0x33u);
  EXPECT_EQ(after_drive, 0x77u);
}

TEST(SyncDriveSignals, MultipleClockingOutputsOnNetResolveByNetType) {
  ClockingSimFixture f;
  auto* n = f.ctx.CreateVariable("n", 4);
  n->value = MakeLogic4VecVal(f.arena, 4, 0);

  Net net;
  net.resolved = n;
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0000));
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());

  net.type = NetType::kWand;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0000u);

  net.type = NetType::kWor;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0001u);
}

TEST(SyncDriveSignals, DriveAndNonblockingAssignToSameVariableBothApply) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  bool nba_ran = false;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("cb", "v", 0x55, f.ctx, f.scheduler);
    auto* nba = f.scheduler.GetEventPool().Acquire();
    nba->callback = [&]() {
      nba_ran = true;
      v->value = MakeLogic4VecVal(f.arena, 8, 0xAA);
    };
    f.scheduler.ScheduleEvent(f.scheduler.CurrentTime(), Region::kNBA, nba);
  });

  uint64_t after = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 12, &after);
  f.scheduler.Run();

  EXPECT_TRUE(nba_ran);
  EXPECT_EQ(after, 0x55u);
}

TEST(SyncDriveSignalsSim, DrivesOfOneVariableFromSourceTakeTheLastOrEachEdge) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  logic [3:0] nibble = 0;\n"
                 "  logic [7:0] v = 0, j = 0, k = 0, h = 0, q = 0;\n"
                 "  int nn = 0;\n"
                 "  string jl = \"\", kl = \"\", hl = \"\";\n"
                 "  default clocking pe @(posedge clk);\n"
                 "    output nibble, v, h, q;\n"
                 "  endclocking\n"
                 "  clocking pj @(posedge clk); output j; endclocking\n"
                 "  clocking nj @(negedge clk); output j; endclocking\n"
                 "  clocking ek @(edge clk); output k; endclocking\n"
                 "  always @(nibble) nn++;\n"
                 "  always @(j) jl = {jl, $sformatf(\"%0t:%0d \", $time, j)};\n"
                 "  always @(k) kl = {kl, $sformatf(\"%0t:%0d \", $time, k)};\n"
                 "  always @(h) hl = {hl, $sformatf(\"%0t:%0d \", $time, h)};\n"
                 "  initial begin\n"
                 "    ##2;\n"
                 "    pe.nibble <= 4'b0101;\n"
                 "    pe.nibble <= 4'b0011;\n"
                 "  end\n"
                 "  initial begin\n"
                 "    #7 pe.v <= 8'd1;\n"
                 "    #1 pe.v <= 8'd2;\n"
                 "  end\n"
                 "  initial begin\n"
                 "    @(pj) pj.j <= 8'd1;\n"
                 "    @(nj) nj.j <= 8'd2;\n"
                 "    @(nj);\n"
                 "    @(pj) pj.j <= 8'd3;\n"
                 "  end\n"
                 "  initial begin\n"
                 "    @(ek) ek.k <= 8'd1;\n"
                 "    @(ek) ek.k <= 8'd2;\n"
                 "    @(ek);\n"
                 "    @(ek) ek.k <= 8'd3;\n"
                 "  end\n"
                 "  initial begin\n"
                 "    #1 h = 8'd7;\n"
                 "    #30 pe.h <= 8'd9;\n"
                 "  end\n"
                 "  initial begin\n"
                 "    @(pe);\n"
                 "    pe.q <= 8'd4;\n"
                 "    q <= 8'd5;\n"
                 "  end\n"
                 "  initial #50 begin\n"
                 "    $display(\"nibble=%b n=%0d v=%0d\", nibble, nn, v);\n"
                 "    $display(\"%s\", jl);\n"
                 "    $display(\"%s\", kl);\n"
                 "    $display(\"%s\", hl);\n"
                 "    $display(\"qok=%0d\", q == 4 || q == 5);\n"
                 "    $finish;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "nibble=0011 n=1 v=2\n5:1 10:2 25:3 \n5:1 10:2 20:3 \n1:7 35:9 "
      "\nqok=1\n$finish at time 50\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SyncDriveSignalsSim, DrivesInSuccessiveReNbaPassesGlitchTheVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  bit a = 1'b1;\n"
                 "  bit x = 0;\n"
                 "  string al = \"\";\n"
                 "  default clocking cb @(posedge clk);\n"
                 "    output a;\n"
                 "  endclocking\n"
                 "  always @(a) al = {al, $sformatf(\"%0t:%b \", $time, a)};\n"
                 "  always @(a) x = ~x;\n"
                 "  initial begin\n"
                 "    ## 1;\n"
                 "    cb.a <= 1'b0;\n"
                 "    @(x);\n"
                 "    cb.a <= 1'b1;\n"
                 "  end\n"
                 "  initial #20 begin $display(\"%s\", al); $finish; end\n"
                 "endmodule\n",
                 f),
      "5:0 5:1 \n$finish at time 20\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SyncDriveSignalsSim, DrivesInSuccessiveReNbaPassesGlitchTheNet) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  wire w;\n"
                 "  bit x = 0;\n"
                 "  string wl = \"\";\n"
                 "  default clocking cb @(posedge clk);\n"
                 "    output w;\n"
                 "  endclocking\n"
                 "  always @(w) wl = {wl, $sformatf(\"%0t:%b \", $time, w)};\n"
                 "  always @(w) if ($time == 5) x = ~x;\n"
                 "  initial begin\n"
                 "    ## 1;\n"
                 "    cb.w <= 1'b0;\n"
                 "    @(x);\n"
                 "    cb.w <= 1'b1;\n"
                 "  end\n"
                 "  initial #20 begin $display(\"%s\", wl); $finish; end\n"
                 "endmodule\n",
                 f),
      "5:0 5:1 \n$finish at time 20\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SyncDriveSignalsSim,
     DISABLED_AProgramsSecondDriveInTheTimeStepGlitchesTheVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program tb(input logic clk);\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output a = m.a;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    @(cb);\n"
                 "    cb.a <= 1'b0;\n"
                 "    @(m.a);\n"
                 "    cb.a <= 1'b1;\n"
                 "    #10;\n"
                 "  end\n"
                 "endprogram\n"
                 "module m;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  bit a = 1'b1;\n"
                 "  string al = \"\";\n"
                 "  always @(a) al = {al, $sformatf(\"%0t:%b \", $time, a)};\n"
                 "  tb t(clk);\n"
                 "  initial #12 $display(\"%s\", al);\n"
                 "endmodule\n",
                 f),
      "5:0 5:1 \n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SyncDriveSignalsSim,
     DISABLED_SeveralClockingOutputsOnANetResolveByItsType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  logic clk = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  wire w;\n"
          "  wand wa;\n"
          "  wor wo;\n"
          "  tri0 t0;\n"
          "  tri1 t1;\n"
          "  trireg tr;\n"
          "  wire pn, z;\n"
          "  logic v;\n"
          "  clocking c1 @(posedge clk); output w, wa, wo, t0, t1, tr, z, v; "
          "endclocking\n"
          "  clocking c2 @(posedge clk); output w, wa, wo, t0, t1, tr, z, v; "
          "endclocking\n"
          "  clocking cp @(posedge clk); output pn; endclocking\n"
          "  clocking cn @(negedge clk); output pn; endclocking\n"
          "  initial begin\n"
          "    @(c1);\n"
          "    c1.w <= 1; c1.wa <= 1; c1.wo <= 1; c1.tr <= 1; c1.z <= 1'b0; "
          "c1.v <= 1;\n"
          "    c1.t0 <= 1'bz; c1.t1 <= 1'bz;\n"
          "    c2.w <= 0; c2.wa <= 0; c2.wo <= 0; c2.tr <= 0; c2.v <= 0;\n"
          "    c2.t0 <= 1'bz; c2.t1 <= 1'bz;\n"
          "    c2.z <= 1'bz;\n"
          "    #1 $display(\"w=%b wa=%b wo=%b t0=%b t1=%b tr=%b z=%b v=%b\", "
          "w, wa, wo, t0, t1, tr, z, v);\n"
          "  end\n"
          "  initial begin\n"
          "    @(cp) cp.pn <= 1;\n"
          "    @(cn) cn.pn <= 0;\n"
          "    #1 $display(\"pn=%b\", pn);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "w=x wa=0 wo=1 t0=0 t1=1 tr=x z=0 v=0\npn=x\n$finish at time 11\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
