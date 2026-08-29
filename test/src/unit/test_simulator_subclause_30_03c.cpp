// What a run registers for the specify block of a module the design
// instantiates, rather than one elaborated as the top.
//
// test_simulator_subclause_30_03a.cpp and test_simulator_subclause_30_03b.cpp
// both declare every specify block in the module ElaborateSrc elaborates as the
// top, so both pass against a Lowerer::Lower that walks the top module alone.
// Issue #3383 is that gap: Lowerer::Lower registered
// RtlirModule::specify_blocks for the top and for no instance, so an
// instantiated module's specify block was parsed, elaborated and then dropped.
// §30.2 makes that the ordinary case rather than a corner of one -- module path
// delays are there to "describe delays for structural models such as ASIC
// cells", and a cell is a thing a design instantiates. §30.3 puts the specify
// block inside a module declaration, which is why two instances of one cell
// declare paths whose src_port and dst_port are the same two strings;
// PathDelay::inst_prefix in src/simulator/specify_path_delay.h is what tells
// those apart, and every case here reads it.
//
// The literals are picked so that no two quantities a case tells apart share a
// value, and so that none is the 0 that SpecifyManager::GetPathDelay answers
// for a path it does not hold. The four sources declare the delays 5, 13, 21,
// 34 and 8, all distinct across the file: 21 and 34 are what
// TwoCellsWithTheSamePortNamesKeepTheirOwnDelays reads apart, and neither is 5,
// so a case that answered out of another case's registration would be caught.
// Nothing here is asserted at zero.
//
// Every source puts the cell first and the top last, because
// ElaborateSrc in lib/cpp/test_fixtures/fixture_simulator.h elaborates
// cu->modules.back()->name.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// The manager `src` leaves installed on `f.ctx` once it has been elaborated,
// lowered and run. Null when the source did not elaborate, so a case asserts on
// the pointer before it reads anything through it.
SpecifyManager* ManagerAfterRunning(SimFixture& f, const std::string& src) {
  auto* elaborated = ElaborateSrc(src, f);
  if (elaborated == nullptr) return nullptr;
  LowerAndRun(elaborated, f);
  return f.ctx.GetSpecifyManager();
}

// The registered module path ending at output port `dst`, whichever instance
// declared it. Used by the case whose subject is that any path was registered
// at all, which cannot name an instance prefix before it has read one.
const PathDelay* PathEndingAt(const SpecifyManager& mgr, std::string_view dst) {
  for (const auto& entry : mgr.GetPathDelays()) {
    if (entry.dst_port == dst) return &entry;
  }
  return nullptr;
}

// The registered module path ending at output port `dst` of the instance whose
// hierarchical prefix is `prefix`. Two instances of one cell declare paths with
// identical port names, so the prefix is the only thing that separates them.
const PathDelay* PathInInstance(const SpecifyManager& mgr,
                                std::string_view prefix, std::string_view dst) {
  for (const auto& entry : mgr.GetPathDelays()) {
    if (entry.inst_prefix == prefix && entry.dst_port == dst) return &entry;
  }
  return nullptr;
}

// §30.3: the module path a specify block declares reaches the run when the
// module holding that block is instantiated rather than elaborated as the top.
// The path is read back with its inst_prefix, so the case says the path belongs
// to instance u1 rather than only that some path was registered.
TEST(SpecifyBlockOfInstantiatedCell, InstantiatedCellRegistersItsModulePath) {
  SimFixture f;
  SpecifyManager* mgr = ManagerAfterRunning(f,
                                            "module cell(input a, output y);\n"
                                            "  specify\n"
                                            "    (a => y) = 5;\n"
                                            "  endspecify\n"
                                            "endmodule\n"
                                            "module top;\n"
                                            "  logic out;\n"
                                            "  cell u1(1'b0, out);\n"
                                            "endmodule\n");
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = PathEndingAt(*mgr, "y");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 5u);
  EXPECT_EQ(path->inst_prefix, "u1.");
}

// §30.3: each instance of a cell declares its own module path, so a cell
// instantiated twice registers two. The two entries carry the same src_port and
// dst_port and differ only in inst_prefix, which is the pair a manager keyed on
// port names alone could not hold.
TEST(SpecifyBlockOfInstantiatedCell, TwoInstancesOfOneCellRegisterSeparately) {
  SimFixture f;
  SpecifyManager* mgr = ManagerAfterRunning(f,
                                            "module cell(input a, output y);\n"
                                            "  specify\n"
                                            "    (a => y) = 13;\n"
                                            "  endspecify\n"
                                            "endmodule\n"
                                            "module top;\n"
                                            "  logic first_out;\n"
                                            "  logic second_out;\n"
                                            "  cell u1(1'b0, first_out);\n"
                                            "  cell u2(1'b0, second_out);\n"
                                            "endmodule\n");
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->PathDelayCount(), 2u);
  const PathDelay* first = PathInInstance(*mgr, "u1.", "y");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->delays[0], 13u);
  const PathDelay* second = PathInInstance(*mgr, "u2.", "y");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->delays[0], 13u);
}

// §30.4: a specify block names its terminals by the port names of the module
// holding it, so two unrelated cells may both declare a path from `a` to `y`.
// Each instance's path has to keep the delay its own cell declared; the two
// delays are 21 and 34, so an answer taken from the wrong cell reads as the
// other value rather than as the right one.
TEST(SpecifyBlockOfInstantiatedCell,
     TwoCellsWithTheSamePortNamesKeepTheirOwnDelays) {
  SimFixture f;
  SpecifyManager* mgr =
      ManagerAfterRunning(f,
                          "module latch_cell(input a, output y);\n"
                          "  specify\n"
                          "    (a => y) = 21;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module mux_cell(input a, output y);\n"
                          "  specify\n"
                          "    (a => y) = 34;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module top;\n"
                          "  logic latch_out;\n"
                          "  logic mux_out;\n"
                          "  latch_cell u1(1'b0, latch_out);\n"
                          "  mux_cell u2(1'b0, mux_out);\n"
                          "endmodule\n");
  ASSERT_NE(mgr, nullptr);
  const PathDelay* from_latch = PathInInstance(*mgr, "u1.", "y");
  ASSERT_NE(from_latch, nullptr);
  EXPECT_EQ(from_latch->delays[0], 21u);
  const PathDelay* from_mux = PathInInstance(*mgr, "u2.", "y");
  ASSERT_NE(from_mux, nullptr);
  EXPECT_EQ(from_mux->delays[0], 34u);
}

// §30.7.4.1: a pulsestyle_ondetect declaration selects the on-detect style for
// the module path output it names, and on-event is the style for an output with
// no declaration. Both cells call their output `y`, and only ondetect_cell
// declares a style, so SpecifyManager::ResolvePulseStyle has to answer on the
// instance-qualified name: on-detect for u1.y and on-event for u2.y. A style
// map keyed on the bare port name would answer on-detect to both.
TEST(SpecifyBlockOfInstantiatedCell,
     PulseStyleStaysInTheInstanceThatDeclaredIt) {
  SimFixture f;
  SpecifyManager* mgr =
      ManagerAfterRunning(f,
                          "module ondetect_cell(input a, output y);\n"
                          "  specify\n"
                          "    pulsestyle_ondetect y;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module plain_cell(input a, output y);\n"
                          "  specify\n"
                          "    (a => y) = 8;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module top;\n"
                          "  logic styled_out;\n"
                          "  logic plain_out;\n"
                          "  ondetect_cell u1(1'b0, styled_out);\n"
                          "  plain_cell u2(1'b0, plain_out);\n"
                          "endmodule\n");
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->ResolvePulseStyle("u1.y"), PulseStyle::kOnDetect);
  EXPECT_EQ(mgr->ResolvePulseStyle("u2.y"), PulseStyle::kOnEvent);
}

}  // namespace
