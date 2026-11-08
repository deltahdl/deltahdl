#include <gtest/gtest.h>

#include <string>

#include "fixture_config_run.h"
#include "fixture_scratch_dir.h"

using namespace delta;

namespace {

constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.v;\n"
    "library gateLib adder.vg;\n";

constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n";

constexpr const char* kRtlAdderSource =
    "module adder;\n"
    "  sub s();\n"
    "  initial $display(\"%m rtl-adder\");\n"
    "endmodule\n"
    "module sub;\n"
    "  initial $display(\"%m rtl-sub\");\n"
    "endmodule\n";

constexpr const char* kGateAdderSource =
    "module adder;\n"
    "  sub s();\n"
    "  initial $display(\"%m gate-adder\");\n"
    "endmodule\n"
    "module sub;\n"
    "  initial $display(\"%m gate-sub\");\n"
    "endmodule\n";

constexpr const char* kSelectingConfig =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

constexpr const char* kPlainConfig =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, BoundDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kRtlAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kGateAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

TEST(ConfigSelectsTheRunningSource, EachInstanceRunsTheDescriptionBoundToIt) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  EXPECT_TRUE(ReportsLine(out, "top.a1 rtl-adder")) << out;
  EXPECT_TRUE(ReportsLine(out, "top.a2 gate-adder")) << out;
}

TEST(ConfigSelectsTheRunningSource,
     StruckInstanceClauseLeavesBothInstancesOnTheDefault) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfiguredDesign(tmp, design, kPlainConfig, "cfg2");
  EXPECT_TRUE(ReportsLine(out, "top.a1 rtl-adder")) << out;
  EXPECT_TRUE(ReportsLine(out, "top.a2 rtl-adder")) << out;
  EXPECT_FALSE(ReportsLine(out, "gate-adder")) << out;
}

TEST(ConfigSelectsTheRunningSource,
     EveryInstanceBelowTheNamedOneRunsItsBoundDescription) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  EXPECT_TRUE(ReportsLine(out, "top.a1.s rtl-sub")) << out;
  EXPECT_TRUE(ReportsLine(out, "top.a2.s gate-sub")) << out;
}

}  // namespace
