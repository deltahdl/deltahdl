#include <gtest/gtest.h>

#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "driver/cli_options.h"
#include "driver/protect_license_libraries.h"
#include "driver/source_units.h"
#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "helpers_include_test_dir.h"
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

struct ScopeRun {
  std::string severity;
  std::string scope;
  bool runtime_errors;
  bool stopped;
  uint64_t after;
};

ScopeRun RunAndRecord(const char* src, bool run_finals) {
  SimFixture f;
  RunSeveritySource(f, src);
  if (run_finals) f.scheduler.EndSimulation();
  auto* after = f.ctx.FindVariable("after");
  return {std::string(f.ctx.LastSeverity()),
          std::string(f.ctx.LastSeverityScope()), f.ctx.HasRuntimeErrors(),
          f.ctx.StopRequested(),
          after != nullptr ? after->value.ToUint64() : 0};
}

constexpr std::pair<const char*, const char*> kFatalPlaces[] = {
    {"a task",
     "module t;\n"
     "  int after;\n"
     "  task tk();\n"
     "    $fatal(0, \"f\");\n"
     "  endtask\n"
     "  initial tk();\n"
     "  initial #5 after = 1;\n"
     "endmodule\n"},
    {"a function",
     "module t;\n"
     "  int after;\n"
     "  function int fn();\n"
     "    $fatal(0, \"f\");\n"
     "    return 1;\n"
     "  endfunction\n"
     "  int r;\n"
     "  initial r = fn();\n"
     "  initial #5 after = 1;\n"
     "endmodule\n"},
    {"a class method",
     "class C;\n"
     "  function void m();\n"
     "    $fatal(0, \"f\");\n"
     "  endfunction\n"
     "endclass\n"
     "module t;\n"
     "  int after;\n"
     "  C h = new;\n"
     "  initial h.m();\n"
     "  initial #5 after = 1;\n"
     "endmodule\n"},
    {"a program",
     "program t;\n"
     "  int after;\n"
     "  initial $fatal(0, \"f\");\n"
     "  initial #5 after = 1;\n"
     "endprogram\n"}};

TEST(SeveritySystemTaskSim, AFatalReachedFromEveryPlaceEndsTheRunWithAnError) {
  for (const auto& [where, src] : kFatalPlaces) {
    ScopeRun r = RunAndRecord(src, false);
    EXPECT_EQ(r.severity, "FATAL") << where;
    EXPECT_TRUE(r.runtime_errors) << where;
    EXPECT_EQ(r.after, 0u) << where;
  }
}

TEST(SeveritySystemTaskSim, AFatalInAFinalProcedureStopsTheRunWithAnError) {
  ScopeRun r = RunAndRecord(
      "module t;\n"
      "  final $fatal(0, \"f\");\n"
      "endmodule\n",
      true);
  EXPECT_EQ(r.severity, "FATAL");
  EXPECT_TRUE(r.stopped);
  EXPECT_TRUE(r.runtime_errors);
}

std::string RunCaptureBothStreams(const std::string& src) {
  std::ostringstream err;
  std::streambuf* old = std::cerr.rdbuf(err.rdbuf());
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::cerr.rdbuf(old);
  return out + err.str();
}

constexpr std::pair<const char*, const char*> kWarningPlaces[] = {
    {"a task",
     "module t;\n"
     "  int after;\n"
     "  task tk();\n"
     "    $warning(\"w\");\n"
     "  endtask\n"
     "  initial begin\n"
     "    tk();\n"
     "    after = 1;\n"
     "  end\n"
     "endmodule\n"},
    {"a function",
     "module t;\n"
     "  int after;\n"
     "  function int fn();\n"
     "    $warning(\"w\");\n"
     "    return 1;\n"
     "  endfunction\n"
     "  initial begin\n"
     "    after = fn();\n"
     "  end\n"
     "endmodule\n"},
    {"a class method",
     "class C;\n"
     "  function void m();\n"
     "    $warning(\"w\");\n"
     "  endfunction\n"
     "endclass\n"
     "module t;\n"
     "  int after;\n"
     "  C h = new;\n"
     "  initial begin\n"
     "    h.m();\n"
     "    after = 1;\n"
     "  end\n"
     "endmodule\n"},
    {"a program",
     "program t;\n"
     "  int after;\n"
     "  initial begin\n"
     "    $warning(\"w\");\n"
     "    after = 1;\n"
     "  end\n"
     "endprogram\n"}};

TEST(SeveritySystemTaskSim,
     AWarningFromEveryPlaceLetsTheRunContinueWithoutAnError) {
  for (const auto& [where, src] : kWarningPlaces) {
    ScopeRun r = RunAndRecord(src, false);
    EXPECT_EQ(r.severity, "WARNING") << where;
    EXPECT_FALSE(r.runtime_errors) << where;
    EXPECT_EQ(r.after, 1u) << where;
  }
}

constexpr std::pair<const char*, const char*> kErrorPlaces[] = {
    {"a task",
     "module t;\n"
     "  int after;\n"
     "  task tk();\n"
     "    $error(\"e\");\n"
     "  endtask\n"
     "  initial begin\n"
     "    tk();\n"
     "    after = 1;\n"
     "  end\n"
     "endmodule\n"},
    {"a function",
     "module t;\n"
     "  int after;\n"
     "  function int fn();\n"
     "    $error(\"e\");\n"
     "    return 1;\n"
     "  endfunction\n"
     "  initial begin\n"
     "    after = fn();\n"
     "  end\n"
     "endmodule\n"},
    {"a class method",
     "class C;\n"
     "  function void m();\n"
     "    $error(\"e\");\n"
     "  endfunction\n"
     "endclass\n"
     "module t;\n"
     "  int after;\n"
     "  C h = new;\n"
     "  initial begin\n"
     "    h.m();\n"
     "    after = 1;\n"
     "  end\n"
     "endmodule\n"},
    {"a program",
     "program t;\n"
     "  int after;\n"
     "  initial begin\n"
     "    $error(\"e\");\n"
     "    after = 1;\n"
     "  end\n"
     "endprogram\n"},
    {"a final procedure",
     "module t;\n"
     "  int after;\n"
     "  final begin\n"
     "    $error(\"e\");\n"
     "    after = 1;\n"
     "  end\n"
     "endmodule\n"}};

TEST(SeveritySystemTaskSim,
     AnErrorFromEveryPlaceRecordsAnErrorAndTheRunContinues) {
  for (const auto& [where, src] : kErrorPlaces) {
    ScopeRun r = RunAndRecord(src, true);
    EXPECT_EQ(r.severity, "ERROR") << where;
    EXPECT_TRUE(r.runtime_errors) << where;
    EXPECT_FALSE(r.stopped) << where;
    EXPECT_EQ(r.after, 1u) << where;
  }
}

TEST(SeveritySystemTaskSim, InfoLeavesTheRunWithNoRuntimeError) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  initial $info(\"i\");\n"
                    "endmodule\n");
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
  EXPECT_FALSE(f.ctx.HasRuntimeErrors());
  EXPECT_FALSE(f.ctx.StopRequested());
}

TEST(SeveritySystemTaskSim, EveryPrintedMessageNamesItsSeverity) {
  EXPECT_EQ(RunCaptureBothStreams("module t;\n"
                                  "  initial begin\n"
                                  "    $warning(\"w\");\n"
                                  "    $error(\"e\");\n"
                                  "    $fatal(0, \"f\");\n"
                                  "  end\n"
                                  "endmodule\n"),
            "[0] WARNING t (<test>:3): w\n"
            "[0] ERROR t (<test>:4): e\n"
            "[0] FATAL t (<test>:5): f\n");
}

TEST(SeveritySystemTaskSim, AFatalMessageIsFormattedAsDisplayFormatsIt) {
  SimFixture f;
  RunSeveritySource(f,
                    "module t;\n"
                    "  int v = 7;\n"
                    "  initial $fatal(1, \"v=%0d w=%h\", v, 8'hA5);\n"
                    "endmodule\n");
  EXPECT_EQ(f.ctx.LastSeverity(), "FATAL");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "v=7 w=a5");
}

TEST(SeveritySystemTaskSim, AMessageWithoutUserTextIsTheHeaderAlone) {
  EXPECT_EQ(RunCaptureBothStreams("module t;\n"
                                  "  initial begin\n"
                                  "    $info;\n"
                                  "    $warning();\n"
                                  "    $error;\n"
                                  "    $fatal(0);\n"
                                  "  end\n"
                                  "endmodule\n"),
            "[0] INFO t (<test>:3)\n"
            "[0] WARNING t (<test>:4)\n"
            "[0] ERROR t (<test>:5)\n"
            "[0] FATAL t (<test>:6)\n");
}

std::string ScopeOf(const std::string& src) {
  SimFixture f;
  RunSeveritySource(f, src);
  return std::string(f.ctx.LastSeverityScope());
}

TEST(SeveritySystemTaskSim, AMessageNamesTheInstancePathOfANonTopInstance) {
  EXPECT_EQ(ScopeOf("module sub;\n"
                    "  initial $info(\"i\");\n"
                    "endmodule\n"
                    "module t;\n"
                    "  sub u();\n"
                    "endmodule\n"),
            "t.u");
  EXPECT_EQ(ScopeOf("module sub;\n"
                    "  initial begin : b\n"
                    "    $info(\"i\");\n"
                    "  end\n"
                    "endmodule\n"
                    "module t;\n"
                    "  sub u();\n"
                    "endmodule\n"),
            "t.u.b");
}

TEST(SeveritySystemTaskSim, AMessageNamesTheTaskOrFunctionItIsCalledIn) {
  EXPECT_EQ(ScopeOf("module t;\n"
                    "  task tk();\n"
                    "    $info(\"i\");\n"
                    "  endtask\n"
                    "  initial tk();\n"
                    "endmodule\n"),
            "t.tk");
  EXPECT_EQ(ScopeOf("module t;\n"
                    "  function int fn();\n"
                    "    $info(\"i\");\n"
                    "    return 1;\n"
                    "  endfunction\n"
                    "  int r;\n"
                    "  initial r = fn();\n"
                    "endmodule\n"),
            "t.fn");
}

TEST(SeveritySystemTaskSim, DISABLED_AMessageFromAClassMethodNamesTheMethod) {
  std::string scope = ScopeOf(
      "class C;\n"
      "  function void m();\n"
      "    $info(\"i\");\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C h = new;\n"
      "  initial h.m();\n"
      "endmodule\n");
  EXPECT_NE(scope, "t");
  EXPECT_NE(scope.find('C'), std::string::npos) << scope;
  EXPECT_EQ(scope.back(), 'm') << scope;
}

TEST(SeveritySystemTaskSim, AMessageNamesThePathThroughAGenerateBlock) {
  EXPECT_EQ(ScopeOf("module t;\n"
                    "  if (1) begin : g\n"
                    "    initial $info(\"i\");\n"
                    "  end\n"
                    "endmodule\n"),
            "t.g");
  EXPECT_EQ(ScopeOf("module t;\n"
                    "  for (genvar i = 0; i < 1; i++) begin : g\n"
                    "    initial $info(\"i\");\n"
                    "  end\n"
                    "endmodule\n"),
            "t.g[0]");
}

std::string HeaderLocationAndUserText(const std::string& line) {
  auto open = line.find(" (");
  auto close = line.find("): ");
  if (open == std::string::npos || close == std::string::npos) return line;
  return line.substr(open + 2, close - open - 2) + "|" +
         line.substr(close + 3, line.size() - close - 4);
}

std::string RunFileThroughTheDriver(const std::string& path) {
  CliOptions opts;
  opts.source_files.push_back(path);
  SimFixture f;
  ProtectLicenseLibraries licenses;
  auto pp = PreprocessSources(opts, f.mgr, f.diag, licenses);
  auto* cu = ParseSource(pp, f.mgr, f.diag, f.arena);
  if (cu == nullptr) return "";
  ApplyPreprocMetadata(cu, pp);
  std::ostringstream out;
  std::streambuf* old = std::cout.rdbuf(out.rdbuf());
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("t");
  if (design != nullptr) {
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
  }
  std::cout.rdbuf(old);
  return out.str();
}

TEST(SeveritySystemTaskSim, AMessageAfterALineDirectiveNamesItsFileAndLine) {
  IncludeTestDir tmp;
  auto path =
      tmp.WriteFile("line.sv",
                    "module t;\n"
                    "`line 40 \"renamed.sv\" 0\n"
                    "  initial $info(\"%s:%0d\", `__FILE__, `__LINE__);\n"
                    "endmodule\n");
  std::string out = RunFileThroughTheDriver(path.string());
  EXPECT_EQ(HeaderLocationAndUserText(out), "renamed.sv:40|renamed.sv:40")
      << out;
}

TEST(SeveritySystemTaskSim, AMessageInAnIncludedFileNamesThatFileAndLine) {
  IncludeTestDir tmp;
  auto inc = tmp.WriteFile(
      "sev.svh", "\n  initial $info(\"%s:%0d\", `__FILE__, `__LINE__);\n");
  std::string src = "module t;\n`include \"";
  src += inc.string();
  src += "\"\nendmodule\n";
  auto path = tmp.WriteFile("top.sv", src);
  std::string out = RunFileThroughTheDriver(path.string());
  std::string where = inc.string();
  where += ":2";
  std::string expected = where;
  expected += "|";
  expected += where;
  EXPECT_EQ(HeaderLocationAndUserText(out), expected) << out;
}

}  // namespace
