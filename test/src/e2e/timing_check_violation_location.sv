// §31.3.1's $setup, violated by the stimulus below, reported at the line the
// check was written on. What is recorded is the whole of what a reader sees:
// the located warning line, the source line echoed beneath it, and the caret
// under the column the check starts at. A unit test can assert the line number
// a report carries, and no unit test asserts the three lines a terminal
// prints, which is what this tier compares.
//
// A Clause 31 timing violation was reported at SourceLoc::None(), whose line
// is 0, until TimingCheckEntry::loc (src/simulator/specify_timing_check.h)
// carried the check's own first token into the report. That is issue #3414,
// and this case is the regression coverage for it.
//
// Syntax 31-3 writes $setup(data_event, reference_event, timing_check_limit),
// so `d` is the data event and `posedge clk` the reference event. §31.3.1 ends
// the window at the reference edge and opens it `limit` time units earlier,
// and reports a violation for a data transition strictly inside it. `d` rises
// at time 5 and `clk` rises at time 10, leaving 5 time units against a limit
// of 10. Both signals are driven to 0 before either transition that matters.
//
// The $setup stands at column 1 so that the caret line printed beneath the
// reported source line is exactly two spaces and a caret:
// src/common/diagnostic.cpp writes "  ", then column - 1 spaces, then "^".
// Every other byte of timing_check_violation_location.expected follows from
// reading the sources.
//
// The specify block is in the top module, which
// Lowerer::RegisterDesignTiming (src/simulator/lowerer.cpp) registers under an
// empty instance prefix, and ReportViolation
// (src/simulator/timing_check_driver.cpp) spells both signal names under that
// prefix. So the message names `d` and `clk` as they are written here.
//
// The design calls no $finish, so the run records no `$finish at time N` line:
// EmitFinishDiagnostic (src/simulator/eval_system_func.cpp) is what prints
// one. It calls no $display either, so standard output is empty and the
// recorded output is the report alone.
module timing_check_violation_location;
  logic d;
  logic clk;

  specify
$setup(d, posedge clk, 10);
  endspecify

  initial begin
    d = 1'b0;
    clk = 1'b0;
    #5 d = 1'b1;
    #5 clk = 1'b1;
  end
endmodule
