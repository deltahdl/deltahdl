#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(SeveritySystemTaskSim, SeverityLevelValues) {
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kInfo), 0);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kWarning), 1);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kError), 2);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kFatal), 3);
}

TEST(SeveritySystemTaskSim, SeverityToString) {
  EXPECT_EQ(SeverityToString(AssertionSeverity::kInfo), "INFO");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kWarning), "WARNING");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kError), "ERROR");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kFatal), "FATAL");
}

// §20.10 "$fatal shall generate a run-time fatal error, which terminates the
// simulation with an error code... Calling $fatal results in an implicit
// call to $finish."
TEST(SeveritySystemTaskSim, FatalRequestsStop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $fatal(1, \"boom\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.StopRequested());
  EXPECT_EQ(f.ctx.LastSeverity(), "FATAL");
}

// §20.10 "The first argument passed to $fatal shall be consistent with the
// corresponding argument to the $finish system task". finish_number ∈
// {0, 1, 2} must all drive the implicit-$finish termination.
TEST(SeveritySystemTaskSim, FatalAllValidFinishNumbersStop) {
  for (int fn = 0; fn <= 2; ++fn) {
    SimFixture f;
    auto src = "module t;\n"
               "  initial $fatal(" + std::to_string(fn) + ", \"x\");\n"
               "endmodule\n";
    auto* design = ElaborateSrc(src, f);
    ASSERT_NE(design, nullptr);
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
    EXPECT_TRUE(f.ctx.StopRequested())
        << "finish_number " << fn << " must trigger implicit $finish";
    EXPECT_EQ(f.ctx.LastSeverity(), "FATAL") << "finish_number " << fn;
  }
}

// §20.10 "$error shall generate a run-time error" — simulation continues.
TEST(SeveritySystemTaskSim, ErrorRecordsButContinues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    $error(\"oops\");\n"
      "    x = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_FALSE(f.ctx.StopRequested());
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// §20.10 "$warning shall generate a run-time warning."
TEST(SeveritySystemTaskSim, WarningRecordsAndContinues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $warning(\"careful\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
  EXPECT_FALSE(f.ctx.StopRequested());
}

// §20.10 "$info shall generate a run-time message of no specific severity."
TEST(SeveritySystemTaskSim, InfoRecordsAndContinues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $info(\"fyi\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
  EXPECT_FALSE(f.ctx.StopRequested());
}

// §20.10 "All of the severity system tasks shall print a tool-specific
// message... [including] the simulation run time at which the severity
// system task is called." The shared helper captures the time alongside the
// message; verify a runtime-issued task records the current sim time.
TEST(SeveritySystemTaskSim, SeverityCapturesSimulationTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    #5 $error(\"late\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityTime().ticks, 5u);
}

// §20.10 "Each of the severity system tasks can include optional
// user-defined information to be reported. The user-defined message shall
// use the same syntax as the $display system task and thus can include any
// number of arguments." — verify $display-style format arguments resolve.
TEST(SeveritySystemTaskSim, ErrorWithFormatArgsRendersDisplaySyntax) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd7;\n"
      "    $error(\"v=%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "v=7");
}

// §20.10 "The tool-specific message shall include the user-defined message
// if specified." — verify the captured user message round-trips verbatim.
TEST(SeveritySystemTaskSim, InfoIncludesUserDefinedMessage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $info(\"hello world\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "hello world");
}

}  // namespace
