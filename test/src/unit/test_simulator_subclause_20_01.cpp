#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

bool RunSource(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

std::string CallingTask(const std::string& name) {
  return "module t;\n"
         "  initial " +
         name +
         ";\n"
         "endmodule\n";
}

std::string CallingFunction(const std::string& call) {
  return "module t;\n"
         "  int x;\n"
         "  initial x = " +
         call +
         ";\n"
         "endmodule\n";
}

std::string NotImplemented(const std::string& name) {
  return name + " is not a system task or system function this tool implements";
}

TEST(UnknownSystemTask, CallToAnUnknownNameIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$notasystemtask(1)")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$notasystemtask"), 3, "20.1"));
}

TEST(UnknownSystemTask, CallToARecognisedNameIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$random")));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnknownSystemTask, AMisspeltDumpTaskIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$dumpvasr")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$dumpvasr"),
                            2, "20.1"));
}

TEST(UnknownSystemTask, ADumpTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$dumpflush")));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnknownSystemTask, AMisspeltAssertionControlTaskIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$assertofff")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$assertofff"),
                            2, "20.1"));
}

TEST(UnknownSystemTask, AnAssertionControlTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingTask("$assertoff")));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnknownSystemTask, AMisspeltGlobalClockingFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$risen_gclk(1)")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotImplemented("$risen_gclk"),
                            3, "20.1"));
}

TEST(UnknownSystemTask, AGlobalClockingFunctionIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f,
                        "module t;\n"
                        "  int x;\n"
                        "  logic clk;\n"
                        "  global clocking @(posedge clk); endclocking\n"
                        "  initial x = $rose_gclk(clk);\n"
                        "endmodule\n"));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnknownSystemTask, AMisspeltCoverageFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$coverage_gett")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotImplemented("$coverage_gett"), 3, "20.1"));
}

TEST(UnknownSystemTask, AMisspeltStochasticQueueFunctionIsReported) {
  SimFixture f;
  ASSERT_TRUE(RunSource(f, CallingFunction("$q_ad(1)")));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NotImplemented("$q_ad"), 3, "20.1"));
}

}  // namespace
