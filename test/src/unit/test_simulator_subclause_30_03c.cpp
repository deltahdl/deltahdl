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

SpecifyManager* ManagerAfterRunning(SimFixture& f, const std::string& src) {
  auto* elaborated = ElaborateSrc(src, f);
  if (elaborated == nullptr) return nullptr;
  LowerAndRun(elaborated, f);
  return f.ctx.GetSpecifyManager();
}

const PathDelay* PathEndingAt(const SpecifyManager& mgr, std::string_view dst) {
  for (const auto& entry : mgr.GetPathDelays()) {
    if (entry.dst_port == dst) return &entry;
  }
  return nullptr;
}

const PathDelay* PathInInstance(const SpecifyManager& mgr,
                                std::string_view prefix, std::string_view dst) {
  for (const auto& entry : mgr.GetPathDelays()) {
    if (entry.inst_prefix == prefix && entry.dst_port == dst) return &entry;
  }
  return nullptr;
}

TEST(SpecifyBlockOfInstantiatedCell, InstantiatedCellRegistersItsModulePath) {
  SimFixture f;
  SpecifyManager* mgr =
      ManagerAfterRunning(f,
                          "module timed_cell(input a, output y);\n"
                          "  specify\n"
                          "    (a => y) = 5;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module top;\n"
                          "  logic out;\n"
                          "  timed_cell u1(1'b0, out);\n"
                          "endmodule\n");
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = PathEndingAt(*mgr, "y");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 5u);
  EXPECT_EQ(path->inst_prefix, "u1.");
}

TEST(SpecifyBlockOfInstantiatedCell, TwoInstancesOfOneCellRegisterSeparately) {
  SimFixture f;
  SpecifyManager* mgr =
      ManagerAfterRunning(f,
                          "module timed_cell(input a, output y);\n"
                          "  specify\n"
                          "    (a => y) = 13;\n"
                          "  endspecify\n"
                          "endmodule\n"
                          "module top;\n"
                          "  logic first_out;\n"
                          "  logic second_out;\n"
                          "  timed_cell u1(1'b0, first_out);\n"
                          "  timed_cell u2(1'b0, second_out);\n"
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
