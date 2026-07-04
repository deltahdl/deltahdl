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

TEST(SeveritySystemTaskSim, FatalAllValidFinishNumbersStop) {
  for (int fn = 0; fn <= 2; ++fn) {
    SimFixture f;
    auto src =
        "module t;\n"
        "  initial $fatal(" +
        std::to_string(fn) +
        ", \"x\");\n"
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

// §20.10: calling $fatal performs an implicit $finish whose first argument (the
// finish_number) is consistent with $finish's argument (§20.2) and selects the
// diagnostic-reporting level. finish_number 2 reports the time plus the
// resource-statistics line, exactly as $finish(2) would. The FATAL banner
// itself is written to stderr, so capturing stdout isolates the implicit
// $finish diagnostic.
TEST(SeveritySystemTaskSim, FatalFinishNumberTwoEmitsFullFinishDiagnostic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $fatal(2, \"boom\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  testing::internal::CaptureStdout();
  f.scheduler.Run();
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out,
            "$finish at time 0\n"
            "$finish: memory and CPU time statistics unavailable\n");
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.10: finish_number 1 (the $finish default reporting level) prints only the
// time banner, with no statistics line.
TEST(SeveritySystemTaskSim, FatalFinishNumberOneEmitsTimeBannerOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial #3 $fatal(1, \"boom\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  testing::internal::CaptureStdout();
  f.scheduler.Run();
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "$finish at time 3\n");
}

// §20.10: finish_number 0 requests no diagnostic output, consistent with
// $finish(0); the implicit $finish still terminates the run.
TEST(SeveritySystemTaskSim, FatalFinishNumberZeroSuppressesDiagnostic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $fatal(0, \"boom\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  testing::internal::CaptureStdout();
  f.scheduler.Run();
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "");
  EXPECT_TRUE(f.ctx.StopRequested());
  EXPECT_EQ(f.ctx.LastSeverity(), "FATAL");
}

// §20.10: when $fatal is called with no finish_number, its implicit $finish
// falls back to the default reporting level (1, per §20.2), printing the time
// banner without the resource-statistics line. Exercises the empty-argument
// branch of the level selection, distinct from an explicit finish_number.
TEST(SeveritySystemTaskSim, FatalWithoutFinishNumberDefaultsToLevelOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $fatal;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  testing::internal::CaptureStdout();
  f.scheduler.Run();
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "$finish at time 0\n");
  EXPECT_TRUE(f.ctx.StopRequested());
  EXPECT_EQ(f.ctx.LastSeverity(), "FATAL");
}

// §20.10: the finish_number that selects the reporting level need not be a
// literal — a parameter (§11.2.1 constant form) supplies the same value through
// a different evaluation path. A parameter of 2 must yield the full level-2
// $finish diagnostic, exactly as the literal 2 does.
TEST(SeveritySystemTaskSim, FatalFinishNumberFromParameterSelectsLevel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int LVL = 2;\n"
      "  initial $fatal(LVL, \"boom\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  testing::internal::CaptureStdout();
  f.scheduler.Run();
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out,
            "$finish at time 0\n"
            "$finish: memory and CPU time statistics unavailable\n");
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.10: the user-defined message uses the $display task syntax (§21.2.1) and
// may carry any number of arguments. A two-argument format confirms every
// argument feeds the shared display machinery, not merely the first.
TEST(SeveritySystemTaskSim, WarningRendersMultipleFormatArguments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = 8'd7;\n"
      "    $warning(\"a=%0d b=%0d\", a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "a=5 b=7");
}

// §20.10: the tool-specific message shall include the hierarchical name of the
// scope in which the severity task is called. A task inside a named block
// reports the top instance joined to that block's name.
TEST(SeveritySystemTaskSim, MessageReportsHierarchicalScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $info(\"hi\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
  EXPECT_EQ(f.ctx.LastSeverityScope(), "t.blk");
}

// §20.10: the message shall include the source line of the call, the same line
// number the `__LINE__ compiler directive would yield there (§22.13). The
// $error call sits on the third source line.
TEST(SeveritySystemTaskSim, MessageReportsSourceLine) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial\n"
      "    $error(\"x\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityLine(), 3u);
}

// §20.10 (final paragraph): an assertion whose action_block has no else (fail)
// clause takes the default fail action, which is a call to $error. A bare
// immediate assert that fails must therefore report ERROR severity even though
// the source names no severity task, and the run continues (unlike $fatal).
TEST(SeveritySystemTaskSim, AssertionDefaultFailActionIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert (1'b0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_FALSE(f.ctx.StopRequested());
}

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
