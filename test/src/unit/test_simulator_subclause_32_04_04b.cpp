// §32.4.4 reaching a real run.
//
// test_simulator_subclause_32_04_04a.cpp binds the design's interconnect
// topology itself and applies each entry directly, which tests the matching
// rules and nothing about whether a design ever gets that far. The cases here
// carry one design through the production path alone -- parsed, elaborated,
// lowered and run -- let the $sdf_annotate call the source writes place the
// delay, and read the load's value off the design's own signals on either side
// of the annotated arrival.
//
// The design is one instance whose input port is driven by a signal of the top
// module, which is the shape §32.4.4 annotates across: "INTERCONNECT" carries a
// source and a load, and the load here is `u/din`, the port of instance `u`.
// The instance copies its input straight to its output and the top module reads
// that output, so what the top reads is what arrived at the port.
//
// The literals are chosen so that no two quantities a case tells apart share a
// value: `src` starts at 8'h00 and moves to 8'hA5, the interconnect delay is 10
// time units, and the two samples are taken at 7 and 17 -- one before the
// annotated arrival at 15 and one after. A sample variable starts at 8'hEE, so
// a sample that never ran is told from both values it could have read.

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

// The value `src` starts at, and so the value the load still reads while the
// annotated delay has not elapsed.
constexpr uint64_t kOldValue = 0x00;

// The value `src` moves to, and so the value the load reads once it has.
constexpr uint64_t kNewValue = 0xA5;

// Writes `text` to a real file and returns its path, because §32.9 gives
// $sdf_annotate a file name and the annotator opens it.
std::string WriteSdfFile(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_04_04_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

// One instance `u` whose input port `din` is driven by the top module's `src`,
// with the port's value read back through the instance's output. The two
// samples are taken at times 7 and 17; the $sdf_annotate call is made at time 1
// so that the port connection's first evaluation, at time 0, is not itself
// delayed and `din` stands at kOldValue well before the first sample.
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

// One CELL record carrying `body` as its only ABSOLUTE delay entry.
std::string DelayFile(const std::string& body) {
  return "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY "
         "(ABSOLUTE " +
         body + "))))";
}

// §32.4.4: the load still holds its old value while the annotated delay has
// not elapsed. `src` moves at time 5 and the delay is 10, so the sample at time
// 7 must read what the port held before the move. Without the delay the port
// takes its source's value in the same time step and this sample reads the new
// one.
TEST(InterconnectDelaySim, AnAnnotatedLoadHoldsTheOldValueBeforeTheDelay) {
  const std::string kSdf =
      WriteSdfFile("before.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* early = RunAndFindVar(InterconnectDesign(kSdf), f, "early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kOldValue);
}

// §32.4.4: and it holds the new value once the delay has elapsed. The sample at
// time 17 is after the annotated arrival at time 15, so the value must be
// through; a fix that delayed the load and never released it would leave the
// old value standing here.
TEST(InterconnectDelaySim, AnAnnotatedLoadTakesTheNewValueAfterTheDelay) {
  const std::string kSdf =
      WriteSdfFile("after.sdf", DelayFile("(INTERCONNECT src u/din (10))"));
  SimFixture f;
  auto* late = RunAndFindVar(InterconnectDesign(kSdf), f, "late");
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(late->value.ToUint64(), kNewValue);
}

// The counterpart that keeps the delay attributable to the annotation: the same
// design over a file annotating nothing takes its source's value at once, so
// the early sample reads the new value. Without this a port connection delayed
// unconditionally would pass both cases above.
TEST(InterconnectDelaySim, AnUnannotatedLoadTakesItsSourceValueAtOnce) {
  const std::string kSdf = WriteSdfFile("none.sdf", "(DELAYFILE)");
  SimFixture f;
  auto* early = RunAndFindVar(InterconnectDesign(kSdf), f, "early");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), kNewValue);
}

// The root-cause guard under the three cases above: the run binds the design's
// interconnect connectivity, without which an entry has no port to look its
// names up in and annotates nothing at all. `u/din` is the load every case
// names, so its presence is what says the collector walked the design the
// entries are written against.
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

// Two instances in a chain: u1's output drives the net w, and w drives u2's
// input, so an INTERCONNECT from u1/dout to u2/din names an instance's output
// port as its source. Sampled as InterconnectDesign samples.
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

// §32.4.4 (printed pages 928-929): an INTERCONNECT names a source port and a
// load port and puts its delay between them, so with u1's output port as the
// source u2's input holds its old value until 10 after w moves. The entry was
// stored against the port u1/dout while the run asked for the delay from the
// net u2's connection names, w, and found none: u2 took the new value at once.
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

// §32.9: a cell's INSTANCE names where its entries apply, an interconnect
// entry's ports among them, so the pair inside instance b is annotated: b's
// load still holds the old value 2 after its source changed.
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

// The leaf/top design of the cases above, with the source driven by
// `stimulus`, written inside the initial block after the annotation at 1, and
// the load sampled into `seen` by `sampling`.
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

// §32.4.4 gives an interconnect delay all twelve transition delays, so a
// change to z takes the turn-off delay, 7 of (1) (2) (7), and the load still
// holds 01 at 8, three after the change at 5.
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

// §32.4.4 permits any number of future schedules, so the source moving again
// while the delay is pending is not lost: the load ends at 3C, the value the
// source settled at, rather than the A5 it passed through.
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

// §32.4.4 gives interconnect delays the path delays' pulse limits, which are
// the delay itself by default (§32.7), so a pulse of 3 on the source, narrower
// than the delay of 10, never reaches the load: it holds 01 throughout.
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

// A driver u1 and a load c one level down inside u2, joined by the net w and
// u2's port i. u1 moves from 01 to A5 at 5, and c samples what reaches its din
// at `when` into `seen`.
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

// §32.4.4's down-hierarchy annotation: the source u1/o sits above the load
// u2/c/din, and the change it makes at 5 reaches the load 5 later, so at 8
// the load still holds 01.
TEST(InterconnectDelaySim, ADownHierarchyDelayReachesTheLoadBelow) {
  const std::string kSdf =
      WriteSdfFile("down.sdf", DelayFile("(INTERCONNECT u1/o u2/c/din (5))"));
  SimFixture f;
  auto* seen = RunAndFindVar(HierarchyDesign(kSdf, "8"), f, "u2.c.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 0x01u);
}

// A NETDELAY on w is the delay from w's source to every load port on it, u2/i
// and u2/c/din alike, so the change at 5 reaches u2/c/din at 10, not once per
// level at 15: at 12 the load holds A5.
TEST(InterconnectDelaySim, ANetDelayReachesALoadBelowOnce) {
  const std::string kSdf =
      WriteSdfFile("netdelay.sdf", DelayFile("(NETDELAY w (5))"));
  SimFixture f;
  auto* seen = RunAndFindVar(HierarchyDesign(kSdf, "12"), f, "u2.c.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 0xA5u);
}

// §32.4.4: on a multisource net each source/load pair may carry a delay of
// its own. u1 and u3 both drive w, u1 holding z throughout; u3 moves to A5 at
// 5, and its own delay of 9 is what reaches the load, not u1's 5, so at 12 the
// load still holds z and at 16 it holds A5.
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

// §30.7 with §32.4.4: a pulse between the reject limit and the error limit an
// interconnect value states, ((10) (2) (8)), reaches the load as x. The source
// pulses to FF from 5 to 9, which would reach the load from 15 to 19, a width
// of 4: at 17 the load holds x.
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

// §30.7.4.2 with §32.4.4: a falling change taking 2 that follows a rising one
// taking 10 arrives first and crosses it, so the rising one is dropped. The
// source falls at 5, rises at 9 and falls again at 10: the rise would land at
// 19, the fall after it at 12, and the load stays 00 from 7 on.
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

// §32.4.4: a port connection reading only a constant drives its load once, and
// a delay annotated before the run starts holds that drive back without
// losing it. The connection sends a5 across a delay of 10 at time 0 and has
// nothing further to wait for, yet the port takes a5 at 10, and the output the
// instance copies it to with it: at 7 neither holds a5 yet, at 17 both do.
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

// §32.4.4: an inout port is a load like an input port, and a reference at the
// load sees the delayed value while one before it sees the undelayed value.
// u drives n from 0 to 1 at 2 and the delay from u/o to c/p is 5, so at 4 n
// holds 1 and c.p still 0, and at 8 c.p holds 1. One merged net would show 1
// at c.p from 2 on.
TEST(InterconnectDelaySim, AnInoutLoadSeesTheDelayedValueAndItsNetDoesNot) {
  const std::string kSdf =
      WriteSdfFile("inout_load.sdf", DelayFile("(INTERCONNECT u/o c/p (5))"));
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

// The two nets of an inout port drive each other with what each one's own
// drivers resolve to, so a value the child drives out reaches the parent's net
// and goes away again when the child lets go: c drives p to 1 at 2 and
// releases it at 6, and at 4 n holds 1 and at 8 z. A link that passed each
// net's whole value back would hold the 1 between the two nets for good. The
// design calls $sdf_annotate from a task, which keeps the port's two nets
// apart as a call from a procedure does.
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

// §32.4.4: an inout port is a source as well as a load, so a delay runs from
// one inout port to another on the same net. c1 drives its port to 1 at 2 and
// the delay from c1/p to c2/p is 5: at 4 n holds 1 and c2.p still z, and at 8
// c2.p holds 1.
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

// §32.4.4: a driver the parent itself writes onto the net stands for no port,
// so its delay to an inout load is the one annotated from the net. top drives
// n from 0 to 1 at 2 and the delay from n to c/p is 5, so at 4 n holds 1 and
// c.p still 0, and at 8 c.p holds 1. Looked up from anything but n, the
// driver finds no delay and c.p reads 1 at 4.
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

// §23.3.3.2: a ref port is its connection's variable whether or not the design
// calls $sdf_annotate, which keeps only an inout port's two nets apart. c
// writes r at 2, and at 3 the parent's v reads what c wrote.
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

}  // namespace
