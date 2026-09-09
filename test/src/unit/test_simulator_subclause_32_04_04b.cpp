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
#include <string>

#include "fixture_simulator.h"
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

}  // namespace
