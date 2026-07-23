// §20.17.2 $stacktrace — retrieves the call stack of the context invoking it,
// up to the top-level process, and is callable as either a task (displays the
// text) or a function (returns it as a string). Its content is implementation
// dependent; this build reports the names of the active subroutine frames,
// innermost first. Because the call stack is produced by real subroutine calls
// (§13 tasks and functions) and the returned string lands in a §6.16 string
// variable, these tests build both from source and drive the full pipeline
// (parse → elaborate → lower → run) rather than hand-pushing frames. The rules
// live in stmt_exec.cpp (task form) and eval_system_func.cpp (function form /
// BuildStackTraceReport).
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §20.17.2: called as a task, $stacktrace displays the call stack of the
// invoking context up to the top-level process. Running nested tasks observes
// the displayed chain end to end: inner (the context calling $stacktrace)
// is shown first, then its caller outer.
TEST(Stacktrace, TaskFormDisplaysNestedCallStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  task inner; $stacktrace; endtask\n"
      "  task outer; inner; endtask\n"
      "  initial outer;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "inner\nouter\n");
}

// §20.17.2: the task form invoked straight from a top-level process has no
// enclosing subroutine to report — the walk toward the top-level process ends
// immediately. The display path emits an empty call stack (only the trailing
// newline of the displayed line).
TEST(Stacktrace, TaskFormAtTopLevelDisplaysEmptyStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $stacktrace;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

// §20.17.2: called as a function, $stacktrace returns a string containing the
// call stack information — the LRM's own shape: assigned into a string
// variable for later processing. With the task chain outer -> inner active at
// the capture point, the stored text names both frames, innermost first, and
// survives until the top-level process prints it after the chain has returned.
TEST(Stacktrace, FunctionFormReturnsCallStackStringForLaterProcessing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  task inner; trace = $stacktrace; endtask\n"
      "  task outer; inner; endtask\n"
      "  initial begin\n"
      "    outer;\n"
      "    $display(\"%s\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "inner\nouter\n");
}

// §20.17.2: the function form follows the call stack only up to the top-level
// process. Evaluated directly from a top-level process, with no enclosing
// subroutine frame, it returns an empty string — observed by bracketing the
// displayed value so emptiness is distinguishable from no output at all.
TEST(Stacktrace, FunctionFormAtTopLevelReturnsEmptyString) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  initial begin\n"
      "    trace = $stacktrace;\n"
      "    $display(\"[%s]\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
}

// §20.17.2: the chain from the calling context to the top-level process can
// mix frame kinds — here a function frame produced inside a task frame. The
// reported stack interleaves both in caller order: the function (the context
// calling $stacktrace) first, then the task that invoked it.
TEST(Stacktrace, MixedFunctionInsideTaskReportsBothFrames) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  int unused;\n"
      "  function int probe();\n"
      "    trace = $stacktrace;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  task outer; unused = probe(); endtask\n"
      "  initial begin\n"
      "    outer;\n"
      "    $display(\"%s\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "probe\nouter\n");
}

// §20.17.2: the function form is an ordinary expression, so it also serves as
// a declaration initializer — a distinct syntactic position from the
// procedural assignment the other tests use. A module-level string initialized
// with $stacktrace captures the stack of its (top-level) evaluation context:
// no subroutine frame is active, so the stored text is empty.
TEST(Stacktrace, FunctionFormAsDeclarationInitializerCapturesContext) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace = $stacktrace;\n"
      "  initial $display(\"[%s]\", trace);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
}

// §20.17.2: both calling conventions name the same information — the task form
// displays what the function form returns. Used as a direct operand of
// $display inside the same task frame, the function form's text matches the
// task form's displayed line from that frame.
TEST(Stacktrace, TaskAndFunctionFormsAgreeFromSameFrame) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  task probe;\n"
      "    $stacktrace;\n"
      "    $display(\"%s\", $stacktrace);\n"
      "  endtask\n"
      "  initial probe;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "probe\nprobe\n");
}

}  // namespace
