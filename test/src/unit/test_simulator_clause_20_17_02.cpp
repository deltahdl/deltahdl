#include <gtest/gtest.h>

#include <string>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.17.2: $stacktrace reports the call stack of the context that invokes it,
// working from that context up to the top-level process. Its content is
// implementation dependent; this build reports the names of the active
// subroutine frames, innermost first. These tests drive the simulator's
// $stacktrace handling (eval_function.cpp for the function form that returns the
// string, stmt_exec.cpp for the task form that displays it).

// Decode a string-valued Logic4Vec back into the characters it packs, so the
// text returned by the function form of $stacktrace can be inspected.
std::string DecodeString(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string result;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

// §20.17.2: called as a function, $stacktrace returns a string containing the
// call stack information. With the subroutine chain outer -> inner active, the
// returned text names both frames with the innermost (the context calling
// $stacktrace) reported first.
TEST(Stacktrace, FunctionFormReturnsCallStackString) {
  SimFixture f;
  f.ctx.PushFuncName("outer");
  f.ctx.PushFuncName("inner");
  auto* call = MkSysCall(f.arena, "$stacktrace", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(DecodeString(result), "inner\nouter");
}

// §20.17.2: with a single subroutine frame active, the function form returns
// just that frame's name. This boundary confirms the innermost-first join only
// inserts a separator between frames, leaving a lone frame unadorned.
TEST(Stacktrace, FunctionFormReportsLoneFrameWithoutSeparator) {
  SimFixture f;
  f.ctx.PushFuncName("solo");
  auto* call = MkSysCall(f.arena, "$stacktrace", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(DecodeString(result), "solo");
}

// §20.17.2: the call stack is followed only up to the top-level process. When
// $stacktrace is reached directly from a top-level process, with no enclosing
// subroutine on the stack, there are no frames to report.
TEST(Stacktrace, TopLevelContextHasNoSubroutineFrames) {
  SimFixture f;
  EXPECT_EQ(BuildStackTraceReport(f.ctx), "");
}

// §20.17.2: the task form invoked straight from a top-level process likewise
// has no enclosing subroutine to report. Driving it through the statement
// executor and capturing stdout observes the display path emit an empty call
// stack (only the trailing newline of the displayed line).
TEST(Stacktrace, TaskFormAtTopLevelDisplaysEmptyStack) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $stacktrace;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "\n");
}

// §20.17.2: called as a task, $stacktrace displays the call stack of the
// invoking context up to the top-level process. Running nested tasks and
// capturing stdout observes the displayed chain end to end: inner (the context
// calling $stacktrace) is shown first, then its caller outer.
TEST(Stacktrace, TaskFormDisplaysNestedCallStack) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task inner; $stacktrace; endtask\n"
      "  task outer; inner; endtask\n"
      "  initial outer;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "inner\nouter\n");
}

}  // namespace
