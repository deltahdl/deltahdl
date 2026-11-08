#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sequences.h"

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
  EXPECT_TRUE(f.ctx.HasRuntimeErrors());
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

void RunSeveritySource(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

TEST(SeveritySystemTaskSim, ErrorRendersASformatfArgumentAsItsText) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  int v = 7;\n"
                    "  initial $error($sformatf(\"v is %0d\", v));\n"
                    "endmodule\n");
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "v is 7");
}

TEST(SeveritySystemTaskSim, InfoRendersABareArgumentInDecimal) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  int v = 5;\n"
                    "  initial $info(\"plain\", v);\n"
                    "endmodule\n");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "plain          5");
}

TEST(SeveritySystemTaskSim, ErrorLeavesTheRunWithARuntimeError) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  initial $error(\"e\");\n"
                    "endmodule\n");
  EXPECT_TRUE(f.ctx.HasRuntimeErrors());
}

TEST(SeveritySystemTaskSim, FatalLeavesTheRunWithARuntimeError) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  initial $fatal(0, \"f\");\n"
                    "endmodule\n");
  EXPECT_TRUE(f.ctx.HasRuntimeErrors());
}

TEST(SeveritySystemTaskSim, WarningLeavesTheRunWithNoRuntimeError) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  initial $warning(\"w\");\n"
                    "endmodule\n");
  EXPECT_FALSE(f.ctx.HasRuntimeErrors());
}

TEST(SeveritySystemTaskSim, MessageNamesTheFileAndLineOfTheCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial\n"
                       "    $info(\"here\");\n"
                       "endmodule\n",
                       f),
            "[0] INFO t (<test>:3): here\n");
}

}  // namespace
