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

const PathDelay* FindRegisteredPath(const SpecifyManager& mgr,
                                    std::string_view src,
                                    std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return &pd;
  }
  return nullptr;
}

SpecifyManager* RunAndTakeManager(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

TEST(SpecifyManagerInstalledByRun, RunRegistersDeclaredModulePath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => y) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_TRUE(mgr->HasPathDelay("a", "y"));
  EXPECT_EQ(mgr->GetPathDelay("a", "y"), 5u);
}

TEST(SpecifyManagerInstalledByRun, RunWithoutSpecifyBlockStillInstallsManager) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd44;\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->PathDelayCount(), 0u);
}

TEST(SpecifyManagerInstalledByRun, RegisteredPathStartsWithDefaultPulseLimits) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  specify\n"
      "    (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = FindRegisteredPath(*mgr, "a", "y");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 7u);
  EXPECT_EQ(path->reject_limit[0], 7u);
  EXPECT_EQ(path->error_limit[0], 7u);
}

TEST(SpecifyManagerInstalledByRun, PathSpecificPathPulseNarrowsNamedPath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input clk, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = FindRegisteredPath(*mgr, "clk", "q");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 12u);
  EXPECT_EQ(path->reject_limit[0], 2u);
  EXPECT_EQ(path->error_limit[0], 9u);
}

TEST(SpecifyManagerInstalledByRun, NonPathSpecificPathPulseYieldsToNamedPath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input clk, input data, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "    specparam PATHPULSE$ = (3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* named = FindRegisteredPath(*mgr, "clk", "q");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[0], 12u);
  EXPECT_EQ(named->reject_limit[0], 2u);
  EXPECT_EQ(named->error_limit[0], 9u);
  const PathDelay* unnamed = FindRegisteredPath(*mgr, "data", "q");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->delays[0], 10u);
  EXPECT_EQ(unnamed->reject_limit[0], 3u);
  EXPECT_EQ(unnamed->error_limit[0], 3u);
}

TEST(SpecifyManagerInstalledByRun, RunRegistersPulseStyleDeclaration) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    pulsestyle_ondetect y;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->ResolvePulseStyle("y"), PulseStyle::kOnDetect);

  SimFixture undeclared;
  SpecifyManager* default_mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n",
      undeclared);
  ASSERT_NE(default_mgr, nullptr);
  EXPECT_EQ(default_mgr->ResolvePulseStyle("y"), PulseStyle::kOnEvent);
}

TEST(SpecifyManagerInstalledByRun, RunRegistersShowCancelledDeclaration) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    showcancelled y;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->ResolveShowCancelled("y"), ShowCancelled::kShowcancelled);

  SimFixture undeclared;
  SpecifyManager* default_mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      undeclared);
  ASSERT_NE(default_mgr, nullptr);
  EXPECT_EQ(default_mgr->ResolveShowCancelled("y"),
            ShowCancelled::kNoshowcancelled);
}

}  // namespace
