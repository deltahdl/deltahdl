#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr uint64_t kOldValue = 0x00;

constexpr uint64_t kNewValue = 0xA5;

std::string WriteSdfFile(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_04_04_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

std::string InterconnectDesign(const std::string& sdf_path) {
  return "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
         "  assign dout = din;\n"
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] src = 8'h00;\n"
         "  logic [7:0] out;\n"
         "  logic [7:0] early = 8'hEE;\n"
         "  logic [7:0] late = 8'hEE;\n"
         "  leaf u(.din(src), .dout(out));\n"
         "  initial begin\n"
         "    #1 $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "    #4 src = 8'hA5;\n"
         "    #2 early = out;\n"
         "    #10 late = out;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

std::string DelayFile(const std::string& body) {
  return "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY "
         "(ABSOLUTE " +
         body + "))))";
}

TEST(InterconnectDelaySim, AnAnnotatedLoadHoldsTheOldValueBeforeTheDelay) {
  const std::string kSdf =
      WriteSdfFile("before.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* early = RunAndFindVar(InterconnectDesign(kSdf), f, "early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kOldValue);
}

TEST(InterconnectDelaySim, AnAnnotatedLoadTakesTheNewValueAfterTheDelay) {
  const std::string kSdf =
      WriteSdfFile("after.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* late = RunAndFindVar(InterconnectDesign(kSdf), f, "late");
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(late->value.ToUint64(), kNewValue);
}

TEST(InterconnectDelaySim, AnUnannotatedLoadTakesItsSourceValueAtOnce) {
  const std::string kSdf = WriteSdfFile("none.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* early = RunAndFindVar(InterconnectDesign(kSdf), f, "early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kNewValue);
}

TEST(InterconnectDelaySim, TheRunBindsTheDesignsInterconnectTopology) {
  const std::string kSdf = WriteSdfFile("topology.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* early = RunAndFindVar(InterconnectDesign(kSdf), f, "early");
  ASSERT_NE(early, nullptr);
  SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  bool found = false;
  for (const auto& terminal : mgr->GetInterconnectTopology().terminals) {
    if (terminal.name == "u/din") found = true;
  }
  EXPECT_TRUE(found);
}

std::string ChainDesign(const std::string& sdf_path) {
  return "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
         "  assign dout = din;\n"
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] src = 8'h00;\n"
         "  wire [7:0] w;\n"
         "  logic [7:0] out;\n"
         "  logic [7:0] early = 8'hEE;\n"
         "  logic [7:0] late = 8'hEE;\n"
         "  leaf u1(.din(src), .dout(w));\n"
         "  leaf u2(.din(w), .dout(out));\n"
         "  initial begin\n"
         "    #1 $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "    #4 src = 8'hA5;\n"
         "    #2 early = out;\n"
         "    #10 late = out;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(InterconnectDelaySim, AnInstanceOutputPortIsASourceTheLoadWaitsOn) {
  const std::string kSdf = WriteSdfFile(
      "chain.sdf", DelayFile("(INTERCONNECT u1/dout u2/din (10))"));
  SimFixture early_run;
  auto* early = RunAndFindVar(ChainDesign(kSdf), early_run, "early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kOldValue);
  SimFixture late_run;
  auto* late = RunAndFindVar(ChainDesign(kSdf), late_run, "late");
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(late->value.ToUint64(), kNewValue);
}

TEST(InterconnectDelaySim, ACellsInterconnectReachesThePortsOfItsInstance) {
  const std::string kSdf = WriteSdfFile(
      "region.sdf",
      "(DELAYFILE (CELL (CELLTYPE \"blk\") (INSTANCE top/b) (DELAY "
      "(ABSOLUTE (INTERCONNECT src u/din (10))))))");
  SimFixture f;
  auto* early = RunAndFindVar(
      "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
      "  assign dout = din;\n"
      "endmodule\n"
      "module blk;\n"
      "  logic [7:0] src = 8'h00;\n"
      "  logic [7:0] out;\n"
      "  logic [7:0] early = 8'hEE;\n"
      "  leaf u(.din(src), .dout(out));\n"
      "  initial begin #5 src = 8'hA5; #2 early = out; end\n"
      "endmodule\n"
      "module top;\n"
      "  blk b();\n"
      "  initial #1 $sdf_annotate(\"" +
          kSdf + "\");\nendmodule\n",
      f, "b.early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kOldValue);
}

std::string StimulusDesign(const std::string& sdf_path,
                           const std::string& stimulus,
                           const std::string& sampling) {
  return "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
         "  assign dout = din;\n"
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] src = 8'h01;\n"
         "  logic [7:0] out;\n"
         "  logic [7:0] seen = 8'hEE;\n"
         "  logic ok = 1'b0;\n"
         "  leaf u(.din(src), .dout(out));\n"
         "  initial begin\n"
         "    #1 $sdf_annotate(\"" +
         sdf_path + "\");\n" + stimulus +
         "  end\n"
         "  initial begin\n" +
         sampling +
         "  end\n"
         "endmodule\n";
}

TEST(InterconnectDelaySim, AChangeToZTakesTheTurnOffDelay) {
  const std::string kSdf = WriteSdfFile(
      "turnoff.sdf", DelayFile("(INTERCONNECT src u/din (1) (2) (7))"));
  SimFixture f;
  auto* ok = RunAndFindVar(StimulusDesign(kSdf, "    #4 src = 8'hzz;\n",
                                          "    #8 ok = (out === 8'h01);\n"),
                           f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, ASecondChangeDuringTheDelayReachesTheLoad) {
  const std::string kSdf =
      WriteSdfFile("pending.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* seen = RunAndFindVar(
      StimulusDesign(kSdf, "    #4 src = 8'hA5;\n    #3 src = 8'h3C;\n",
                     "    #40 seen = out;\n"),
      f, "seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 0x3Cu);
}

TEST(InterconnectDelaySim, APulseNarrowerThanTheRejectLimitIsFiltered) {
  const std::string kSdf =
      WriteSdfFile("pulse.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      StimulusDesign(kSdf, "    #4 src = 8'hFF;\n    #3 src = 8'h01;\n",
                     "    #16 ok = (out === 8'h01);\n"),
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

std::string HierarchyDesign(const std::string& sdf_path,
                            const std::string& when) {
  return "module drv(output logic [7:0] o);\n"
         "  logic [7:0] r = 8'h01;\n"
         "  assign o = r;\n"
         "  initial #5 r = 8'hA5;\n"
         "endmodule\n"
         "module sink(input logic [7:0] din);\n"
         "  logic [7:0] seen = 8'hEE;\n"
         "  initial #" +
         when +
         " seen = din;\n"
         "endmodule\n"
         "module mid(input logic [7:0] i);\n"
         "  sink c(.din(i));\n"
         "endmodule\n"
         "module top;\n"
         "  wire [7:0] w;\n"
         "  drv u1(.o(w));\n"
         "  mid u2(.i(w));\n"
         "  initial #1 $sdf_annotate(\"" +
         sdf_path + "\");\nendmodule\n";
}

TEST(InterconnectDelaySim, ADownHierarchyDelayReachesTheLoadBelow) {
  const std::string kSdf =
      WriteSdfFile("down.sdf", DelayFile("(INTERCONNECT u1/o u2/c/din (5))"));
  SimFixture f;
  auto* seen = RunAndFindVar(HierarchyDesign(kSdf, "8"), f, "u2.c.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 0x01u);
}

TEST(InterconnectDelaySim, ANetDelayReachesALoadBelowOnce) {
  const std::string kSdf =
      WriteSdfFile("netdelay.sdf", DelayFile("(NETDELAY w (5))"));
  SimFixture f;
  auto* seen = RunAndFindVar(HierarchyDesign(kSdf, "12"), f, "u2.c.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 0xA5u);
}

TEST(InterconnectDelaySim, EachSourceReachesTheLoadWithItsOwnDelay) {
  const std::string kSdf = WriteSdfFile(
      "multisource.sdf", DelayFile("(INTERCONNECT u1/o u2/din (5))"
                                   " (INTERCONNECT u3/o u2/din (9))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module drv(output logic [7:0] o);\n"
      "  logic [7:0] r = 8'hzz;\n"
      "  assign o = r;\n"
      "endmodule\n"
      "module sink(input logic [7:0] din);\n"
      "  logic ok = 1'b0;\n"
      "  initial begin\n"
      "    #12 ok = (din === 8'hzz);\n"
      "    #4 ok = ok && (din === 8'hA5);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  drv u1(.o(w));\n"
      "  drv u3(.o(w));\n"
      "  sink u2(.din(w));\n"
      "  initial begin\n"
      "    #1 $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #4 u3.r = 8'hA5;\n"
          "  end\n"
          "endmodule\n",
      f, "u2.ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, APulseBetweenTheLimitsReachesTheLoadAsX) {
  const std::string kSdf = WriteSdfFile(
      "pulse_x.sdf", DelayFile("(INTERCONNECT src u/din ((10) (2) (8)))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      StimulusDesign(kSdf, "    #4 src = 8'hFF;\n    #4 src = 8'h01;\n",
                     "    #17 ok = (out === 8'hxx);\n"),
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, ACrossingTransitionDropsTheOneItCrosses) {
  const std::string kSdf = WriteSdfFile(
      "crossing.sdf", DelayFile("(INTERCONNECT src u/din (10) (2))"));
  SimFixture f;
  auto* ok =
      RunAndFindVar(StimulusDesign(kSdf,
                                   "    #4 src = 8'h00;\n    #4 src = 8'h01;\n"
                                   "    #1 src = 8'h00;\n",
                                   "    #20 ok = (out === 8'h00);\n"),
                    f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, AConstantConnectionsPendingDriveStillArrives) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
      "  assign dout = din;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] out;\n"
      "  leaf u(.din(8'hA5), .dout(out));\n"
      "  initial begin\n"
      "    #7 $display(\"%b%b\", u.din === 8'hA5, out === 8'hA5);\n"
      "    #10 $display(\"%b%b\", u.din === 8'hA5, out === 8'hA5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  SdfFile file;
  ASSERT_TRUE(ParseSdf(DelayFile("(PORT u/din (10))"), file));
  AnnotateSdfToManager(file, f.ctx.AcquireSpecifyManager(), SdfMtm::kTypical,
                       {}, "top");
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  f.scheduler.Run();
  std::cout.rdbuf(old_buf);

  EXPECT_EQ(captured.str(), "00\n11\n");
}

void ExpectInoutLoadDelayed(const std::string& stem, const std::string& entry) {
  const std::string kSdf = WriteSdfFile(stem + ".sdf", DelayFile(entry));
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module drv(output wire o);\n"
      "  reg d = 1'b0;\n"
      "  assign o = d;\n"
      "  initial #2 d = 1'b1;\n"
      "endmodule\n"
      "module child(inout wire p);\n"
      "  assign p = 1'bz;\n"
      "endmodule\n"
      "module top;\n"
      "  wire n;\n"
      "  logic ok = 1'b0;\n"
      "  drv u(.o(n));\n"
      "  child c(.p(n));\n"
      "  initial begin\n"
      "    #1 $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #3 ok = (n === 1'b1) && (c.p === 1'b0);\n"
          "    #4 ok = ok && (n === 1'b1) && (c.p === 1'b1);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, AnInoutLoadSeesTheDelayedValueAndItsNetDoesNot) {
  ExpectInoutLoadDelayed("inout_load", "(INTERCONNECT u/o c/p (5))");
}

TEST(InterconnectDelaySim, ANetDelayOnAnInoutPortDelaysTheValueThere) {
  ExpectInoutLoadDelayed("inout_netdelay", "(NETDELAY c/p (5))");
}

TEST(InterconnectDelaySim, AValueAnInoutDrivesOutGoesWhenItLetsGo) {
  const std::string kSdf = WriteSdfFile("inout_out.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module child(inout wire p);\n"
      "  reg e = 1'bz;\n"
      "  assign p = e;\n"
      "  initial begin\n"
      "    #2 e = 1'b1;\n"
      "    #4 e = 1'bz;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  wire n;\n"
      "  logic ok = 1'b0;\n"
      "  child c(.p(n));\n"
      "  task annotate;\n"
      "    $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "  endtask\n"
          "  initial begin\n"
          "    annotate();\n"
          "    #4 ok = (n === 1'b1) && (c.p === 1'b1);\n"
          "    #4 ok = ok && (n === 1'bz) && (c.p === 1'bz);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, AnInoutSourceReachesAnInoutLoadAcrossItsDelay) {
  const std::string kSdf =
      WriteSdfFile("inout_pair.sdf", DelayFile("(INTERCONNECT c1/p c2/p (5))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module child(inout wire p);\n"
      "  reg e = 1'bz;\n"
      "  assign p = e;\n"
      "endmodule\n"
      "module top;\n"
      "  wire n;\n"
      "  logic ok = 1'b0;\n"
      "  child c1(.p(n));\n"
      "  child c2(.p(n));\n"
      "  initial begin\n"
      "    #1 $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #1 c1.e = 1'b1;\n"
          "    #2 ok = (n === 1'b1) && (c2.p === 1'bz);\n"
          "    #4 ok = ok && (c2.p === 1'b1);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, AParentsOwnDriveReachesAnInoutLoadAcrossItsDelay) {
  const std::string kSdf =
      WriteSdfFile("inout_parent.sdf", DelayFile("(INTERCONNECT n c/p (5))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module child(inout wire p);\n"
      "  assign p = 1'bz;\n"
      "endmodule\n"
      "module top;\n"
      "  reg d = 1'b0;\n"
      "  wire n;\n"
      "  logic ok = 1'b0;\n"
      "  assign n = d;\n"
      "  child c(.p(n));\n"
      "  initial begin\n"
      "    #1 $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #1 d = 1'b1;\n"
          "    #2 ok = (n === 1'b1) && (c.p === 1'b0);\n"
          "    #4 ok = ok && (c.p === 1'b1);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, ARefPortSharesItsVariableInADesignThatAnnotates) {
  const std::string kSdf = WriteSdfFile("ref_port.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module child(ref logic [7:0] r);\n"
      "  initial #2 r = 8'h5A;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] v = 8'h00;\n"
      "  logic ok = 1'b0;\n"
      "  child c(.r(v));\n"
      "  initial begin\n"
      "    #1 $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #2 ok = (v === 8'h5A);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, AnInoutInAGenerateBlockKeepsToTheBlocksNet) {
  const std::string kSdf = WriteSdfFile("inout_gen.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* ok = RunAndFindVar(
      "module child(inout wire p);\n"
      "  assign p = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire n;\n"
      "  logic ok = 1'b0;\n"
      "  if (1) begin : g\n"
      "    wire n;\n"
      "    child c(.p(n));\n"
      "  end\n"
      "  initial begin\n"
      "    $sdf_annotate(\"" +
          kSdf +
          "\");\n"
          "    #1 ok = (g.n === 1'b1) && (n === 1'bz);\n"
          "  end\n"
          "endmodule\n",
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim, PendingTransitionsEachReachTheLoadInTurn) {
  const std::string kSdf = WriteSdfFile(
      "in_turn.sdf", DelayFile("(INTERCONNECT src u/din ((10) (0) (0)))"));
  SimFixture f;
  auto* ok = RunAndFindVar(
      StimulusDesign(kSdf, "    #4 src = 8'hA5;\n    #3 src = 8'h3C;\n",
                     "    #16 ok = (out === 8'hA5);\n"
                     "    #3 ok = ok && (out === 8'h3C);\n"),
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

std::string ReportingDesign(const std::string& sdf_path,
                            const std::string& reporting,
                            const std::string& leaf_items = {}) {
  return "module leaf(input logic [7:0] din, output logic [7:0] dout);\n"
         "  assign dout = din;\n" +
         leaf_items +
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] src = 8'h00;\n"
         "  logic [7:0] out;\n"
         "  leaf u(.din(src), .dout(out));\n"
         "  initial begin\n"
         "    #1 $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "    #4 src = 8'hA5;\n"
         "  end\n"
         "  initial begin\n" +
         reporting +
         "  end\n"
         "endmodule\n";
}

TEST(InterconnectDelaySim, DisplayDuringTheDelayShowsTheLoadsOldValue) {
  const std::string kSdf =
      WriteSdfFile("display.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  EXPECT_EQ(RunCapture(ReportingDesign(kSdf,
                                       "    #8 $display(\"%h %h\", "
                                       "u.din, src);\n"),
                       f),
            "00 a5\n");
}

TEST(InterconnectDelaySim, MonitorReportsTheLoadAtTheEndOfTheDelay) {
  const std::string kSdf =
      WriteSdfFile("monitor.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  EXPECT_EQ(RunCapture(ReportingDesign(kSdf, "",
                                       "  initial $monitor(\"%0t %h\", $time, "
                                       "din);\n"),
                       f),
            "0 00\n15 a5\n");
}

std::string SourceDesign(const std::string& sdf_path,
                         const std::string& driver) {
  return driver +
         "module sink(input wire d);\n"
         "endmodule\n"
         "module top;\n"
         "  wire n;\n"
         "  logic ok = 1'b0;\n"
         "  drv u1(.q(n));\n"
         "  sink u2(.d(n));\n"
         "  initial begin\n"
         "    #1 $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "    #6 ok = (n === 1'b1) && (u2.d === 1'b0);\n"
         "    #13 ok = ok && (u2.d === 1'b1);\n"
         "  end\n"
         "endmodule\n";
}

void ExpectSourceWaitsOnTheDelay(const std::string& stem,
                                 const std::string& driver) {
  const std::string kSdf =
      WriteSdfFile(stem + ".sdf", DelayFile("(INTERCONNECT u1/q u2/d (10))"));
  SimFixture f;
  auto* ok = RunAndFindVar(SourceDesign(kSdf, driver), f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

const char* const kUdpDriver =
    "primitive udp_buf(out, in);\n"
    "  output out;\n"
    "  input in;\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n"
    "module drv(output wire q);\n"
    "  reg r = 1'b0;\n"
    "  udp_buf b(q, r);\n"
    "  initial #5 r = 1'b1;\n"
    "endmodule\n";

const char* const kSwitchDriver =
    "module drv(output wire q);\n"
    "  reg r = 1'b0;\n"
    "  wire w;\n"
    "  assign w = r;\n"
    "  tran t(q, w);\n"
    "  initial #5 r = 1'b1;\n"
    "endmodule\n";

const char* const kCheckDriver =
    "module chk(input wire c, input wire r, output wire q);\n"
    "  assign q = dr;\n"
    "  specify\n"
    "    $setuphold(posedge c, r, 1, 1, , , , dc, dr);\n"
    "  endspecify\n"
    "endmodule\n"
    "module drv(output wire q);\n"
    "  reg c = 1'b0;\n"
    "  reg r = 1'b0;\n"
    "  chk k(.c(c), .r(r), .q(q));\n"
    "  initial #5 r = 1'b1;\n"
    "endmodule\n";

TEST(InterconnectDelaySim, AUdpOutputSourceReachesTheLoadAfterTheDelay) {
  ExpectSourceWaitsOnTheDelay("udp_src", kUdpDriver);
}

TEST(InterconnectDelaySim, ASwitchSourceReachesTheLoadAfterTheDelay) {
  ExpectSourceWaitsOnTheDelay("switch_src", kSwitchDriver);
}

TEST(InterconnectDelaySim,
     ATimingCheckDelayedSourceReachesTheLoadAfterTheDelay) {
  ExpectSourceWaitsOnTheDelay("check_src", kCheckDriver);
}

const char* const kPresetDriver =
    "module drv(output wire q);\n"
    "  reg r = 1'b1;\n"
    "  assign #3 q = r;\n"
    "endmodule\n";

const char* const kBareChild =
    "module child(inout wire p);\n"
    "endmodule\n";

const char* const kDrivingChild =
    "module child(inout wire p);\n"
    "  drv k(.q(p));\n"
    "endmodule\n";

std::string WholeNetDesign(const std::string& modules,
                           const std::string& top_items,
                           const std::string& body) {
  return modules + "module top;\n" + top_items +
         "  logic ok = 1'b0;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

void ExpectWholeNetCase(const std::string& stem, const std::string& entry,
                        const std::string& modules,
                        const std::string& top_items,
                        const std::string& checks) {
  const std::string kSdf = WriteSdfFile(stem + ".sdf", DelayFile(entry));
  SimFixture f;
  auto* ok = RunAndFindVar(
      WholeNetDesign(modules, top_items,
                     "    #1 $sdf_annotate(\"" + kSdf + "\");\n" + checks),
      f, "ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

void ExpectOutsideSourceDelayedInside(const std::string& stem,
                                      const std::string& driver) {
  ExpectWholeNetCase(stem, "(INTERCONNECT u1/q c/p (10))", driver + kBareChild,
                     "  wire n;\n  drv u1(.q(n));\n  child c(.p(n));\n",
                     "    #6 ok = (n === 1'b1) && (c.p === 1'b0);\n"
                     "    #13 ok = ok && (c.p === 1'b1);\n");
}

void ExpectInsideSourceSeenOutside(const std::string& stem,
                                   const std::string& driver) {
  ExpectWholeNetCase(stem, "(PORT c/p (10))", driver + kDrivingChild,
                     "  wire n;\n  child c(.p(n));\n",
                     "    #6 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, AUdpOutsideAnInoutPortReachesItAcrossTheDelay) {
  ExpectOutsideSourceDelayedInside("udp_out", kUdpDriver);
}

TEST(InterconnectDelaySim, AUdpInsideAnInoutPortReachesTheNetOutside) {
  ExpectInsideSourceSeenOutside("udp_in", kUdpDriver);
}

TEST(InterconnectDelaySim, ASwitchOutsideAnInoutPortReachesItAcrossTheDelay) {
  ExpectOutsideSourceDelayedInside("switch_out", kSwitchDriver);
}

TEST(InterconnectDelaySim, ASwitchInsideAnInoutPortReachesTheNetOutside) {
  ExpectInsideSourceSeenOutside("switch_in", kSwitchDriver);
}

TEST(InterconnectDelaySim,
     ATimingCheckSignalOutsideAnInoutPortReachesItAcrossTheDelay) {
  ExpectOutsideSourceDelayedInside("check_out", kCheckDriver);
}

TEST(InterconnectDelaySim,
     ATimingCheckSignalInsideAnInoutPortReachesTheNetOutside) {
  ExpectInsideSourceSeenOutside("check_in", kCheckDriver);
}

Variable* RunAnnotatedFromTheStart(const std::string& src,
                                   const std::string& entry, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  SdfFile file;
  EXPECT_TRUE(ParseSdf(DelayFile(entry), file));
  AnnotateSdfToManager(file, f.ctx.AcquireSpecifyManager(), SdfMtm::kTypical,
                       {}, "top");
  f.scheduler.Run();
  return f.ctx.FindVariable("ok");
}

void ExpectPresetCase(const std::string& entry, const std::string& child,
                      const std::string& top_items, const std::string& checks) {
  SimFixture f;
  auto* ok = RunAnnotatedFromTheStart(
      WholeNetDesign(std::string(kPresetDriver) + child, top_items, checks),
      entry, f);
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

TEST(InterconnectDelaySim,
     DISABLED_ADelayedAssignmentsPresetXReachesTheLoadAfterTheDelay) {
  ExpectPresetCase("(INTERCONNECT u1/q u2/d (10))",
                   "module sink(input wire d);\nendmodule\n",
                   "  wire n;\n  drv u1(.q(n));\n  sink u2(.d(n));\n",
                   "    #11 ok = (u2.d === 1'bx);\n"
                   "    #3 ok = ok && (u2.d === 1'b1);\n");
}

TEST(InterconnectDelaySim,
     DISABLED_APresetXOutsideAnInoutPortReachesItAcrossTheDelay) {
  ExpectPresetCase("(INTERCONNECT u1/q c/p (10))", kBareChild,
                   "  wire n;\n  drv u1(.q(n));\n  child c(.p(n));\n",
                   "    #11 ok = (c.p === 1'bx);\n"
                   "    #3 ok = ok && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, APresetXInsideAnInoutPortReachesTheNetOutside) {
  ExpectPresetCase("(PORT c/p (10))", kDrivingChild,
                   "  wire n;\n  child c(.p(n));\n",
                   "    #2 ok = (n === 1'bx);\n"
                   "    #2 ok = ok && (n === 1'b1);\n");
}

void ExpectNetKindOnBothSides(const std::string& stem, const std::string& child,
                              const std::string& top_items,
                              const std::string& checks) {
  ExpectWholeNetCase(stem, "(PORT c/p (10))", child, top_items, checks);
}

TEST(InterconnectDelaySim, DISABLED_ATri0NetOutsideAnInoutPortPullsItLow) {
  ExpectNetKindOnBothSides("tri0_out", kBareChild,
                           "  tri0 n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b0) && (c.p === 1'b0);\n");
}

TEST(InterconnectDelaySim, DISABLED_ATri1NetOutsideAnInoutPortPullsItHigh) {
  ExpectNetKindOnBothSides("tri1_out", kBareChild,
                           "  tri1 n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, DISABLED_ASupply0NetOutsideAnInoutPortHoldsItLow) {
  ExpectNetKindOnBothSides("supply0_out", kBareChild,
                           "  supply0 n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b0) && (c.p === 1'b0);\n");
}

TEST(InterconnectDelaySim, DISABLED_ASupply1NetOutsideAnInoutPortHoldsItHigh) {
  ExpectNetKindOnBothSides("supply1_out", kBareChild,
                           "  supply1 n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, ATri0PortInsidePullsTheNetOutsideLow) {
  ExpectNetKindOnBothSides("tri0_in",
                           "module child(inout tri0 p);\nendmodule\n",
                           "  wire n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b0) && (c.p === 1'b0);\n");
}

TEST(InterconnectDelaySim, ATri1PortInsidePullsTheNetOutsideHigh) {
  ExpectNetKindOnBothSides("tri1_in",
                           "module child(inout tri1 p);\nendmodule\n",
                           "  wire n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, ASupply0PortInsideHoldsTheNetOutsideLow) {
  ExpectNetKindOnBothSides("supply0_in",
                           "module child(inout supply0 p);\nendmodule\n",
                           "  wire n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b0) && (c.p === 1'b0);\n");
}

TEST(InterconnectDelaySim, ASupply1PortInsideHoldsTheNetOutsideHigh) {
  ExpectNetKindOnBothSides("supply1_in",
                           "module child(inout supply1 p);\nendmodule\n",
                           "  wire n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, ATriregOutsideAnInoutPortKeepsItsChargeOnBothSides) {
  ExpectNetKindOnBothSides("trireg_out", kBareChild,
                           "  trireg n;\n  reg e = 1'b1;\n  assign n = e;\n"
                           "  child c(.p(n));\n",
                           "    #4 e = 1'bz;\n"
                           "    #15 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

TEST(InterconnectDelaySim, ATriregPortInsideKeepsItsChargeOnBothSides) {
  ExpectNetKindOnBothSides("trireg_in",
                           "module child(inout trireg p);\n"
                           "  reg e = 1'b1;\n"
                           "  assign p = e;\n"
                           "  initial #5 e = 1'bz;\n"
                           "endmodule\n",
                           "  wire n;\n  child c(.p(n));\n",
                           "    #19 ok = (n === 1'b1) && (c.p === 1'b1);\n");
}

}  // namespace
