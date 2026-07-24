#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1364-1995" region and runs the whole
// pipeline over it — preprocess, parse, elaborate, lower, simulate — returning
// the final value of `var_name`. The diagnostic check is what keeps the result
// meaningful: source the Table 22-1 list admits has to run clean, not merely
// produce a number after the front end recovered from something it rejected.
uint64_t Run1995(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// Words Table 22-1 omits are ordinary identifiers under this list, and they
// carry values at runtime like any other name: this one writes to one, reads
// another back as an operand, and spreads the rest across a hierarchy — the
// child module's name, its two port names, a parameter, a task, and the
// instance name are all words later standards reserve. The value the child
// computes has to reach the parent for the run to produce this result, so
// every one of those names had to resolve.
TEST(Verilog1995KeywordSimulation, FreedWordsRunAcrossAHierarchy) {
  auto result = Run1995(
      "module bit (input wire [7:0] logic, output wire [7:0] byte);\n"
      "  parameter int = 2;\n"
      "  assign byte = logic * int;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] string;\n"
      "  wire [7:0] longint;\n"
      "  reg  [7:0] result;\n"
      "  bit interface (.logic(string), .byte(longint));\n"
      "  task shortint; begin result = longint + 8'd1; end endtask\n"
      "  initial begin\n"
      "    string = 8'd21;\n"
      "    #1 shortint;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The membership side at runtime: the gate primitives and net types Table 22-1
// lists still build working structure under this list, and their values reach
// a variable the run leaves behind.
TEST(Verilog1995KeywordSimulation, ReservedGateAndNetKeywordsDriveValues) {
  auto result = Run1995(
      "module m;\n"
      "  reg  a, b;\n"
      "  wire y, z;\n"
      "  wand w;\n"
      "  reg [7:0] result;\n"
      "  and g1 (y, a, b);\n"
      "  nor g2 (z, a, b);\n"
      "  assign w = a;\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1 result = {5'd0, y, z, w};\n"
      "  end\n"
      "endmodule\n",
      "result");
  // and(1,1) = 1, nor(1,1) = 0, wand of two 1s = 1.
  EXPECT_EQ(result, 5u);
}

// The procedural keywords of Table 22-1 driving real control flow: a loop, a
// count-controlled repeat, a while, and a casez arm all have to be understood
// as keywords for the arithmetic to come out at this value.
TEST(Verilog1995KeywordSimulation, ReservedProceduralKeywordsRun) {
  auto result = Run1995(
      "module m;\n"
      "  integer i;\n"
      "  reg [7:0] result;\n"
      "  reg [1:0] sel;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    for (i = 0; i < 4; i = i + 1) result = result + 8'd5;\n"
      "    repeat (2) result = result + 8'd5;\n"
      "    i = 2;\n"
      "    while (i > 0) begin\n"
      "      result = result + 8'd1;\n"
      "      i = i - 1;\n"
      "    end\n"
      "    sel = 2'b10;\n"
      "    casez (sel)\n"
      "      2'b1?: result = result + 8'd1;\n"
      "      default: result = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

// Table 22-1's event-control and branching words doing their job at runtime:
// an `always` procedure sensitive to a `posedge`/`negedge` list joined by
// `or`, and an `if`/`else` pair choosing between them. The count the run
// leaves behind is reachable only if the sensitivity list and both branches
// were understood as keywords.
TEST(Verilog1995KeywordSimulation, ReservedEventControlAndBranchRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg clk, rst;\n"
      "  reg [7:0] result;\n"
      "  always @(posedge clk or negedge rst)\n"
      "    if (!rst) result <= 8'd40;\n"
      "    else result <= result + 8'd1;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    rst = 1'b1;\n"
      "    #1 rst = 1'b0;\n"
      "    #1 rst = 1'b1;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    #1 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The negedge on rst loads 40, then three posedges each add one.
  EXPECT_EQ(result, 43u);
}

// `wait`, `forever`, and `disable` are Table 22-1 words whose whole meaning is
// a runtime one: the loop has to block until the flag is set, spin, and then be
// torn down by name. Only a run can observe that.
TEST(Verilog1995KeywordSimulation, WaitForeverAndDisableRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg go;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    go = 1'b0;\n"
      "    #2 go = 1'b1;\n"
      "  end\n"
      "  initial begin : blk\n"
      "    result = 8'd40;\n"
      "    wait (go);\n"
      "    forever begin\n"
      "      result = result + 8'd1;\n"
      "      if (result == 8'd43) disable blk;\n"
      "      #1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// A `function` called for its value and a `defparam` overriding a parameter
// across the hierarchy — two more Table 22-1 words whose effect shows up only
// in what the run computes.
TEST(Verilog1995KeywordSimulation, FunctionAndDefparamRun) {
  auto result = Run1995(
      "module sub (output wire [7:0] o);\n"
      "  parameter p = 1;\n"
      "  assign o = p;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  reg  [7:0] result;\n"
      "  sub u (w);\n"
      "  defparam u.p = 21;\n"
      "  function [7:0] twice;\n"
      "    input x;\n"
      "    twice = x ? 8'd2 : 8'd0;\n"
      "  endfunction\n"
      "  initial #1 result = w * twice(1'b1) + 8'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// An `event` declared under this list, triggered with `->`, and waited on by
// an `always` procedure. The keyword, the trigger operator, and the event
// control all have to line up for the waiting process to resume, and the name
// carrying the event is a word a later standard reserved — so the run observes
// both sides of the rule at once.
TEST(Verilog1995KeywordSimulation, FreedWordNamesAnEventDrivingAProcess) {
  auto result = Run1995(
      "module m;\n"
      "  event logic;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    #1 -> logic;\n"
      "  end\n"
      "  always @(logic) result = result + 8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The same arithmetic reached two ways: with the operand written as a literal
// and with it declared as a constant using the Table 22-1 `parameter` keyword.
// The two take different paths to a value, and under this list both have to
// arrive at it — the second also showing `parameter` still declares a constant
// whose name may be a word a later standard reserved.
TEST(Verilog1995KeywordSimulation, LiteralAndParameterConstantsAgree) {
  auto from_literal = Run1995(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = Run1995(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_freed_name = Run1995(
      "module m;\n"
      "  parameter int = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = int * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_freed_name, 43u);
}

// `force`/`release` and the `assign`/`deassign` procedural pair are Table 22-1
// words whose whole effect is a runtime one, so this is the only stage where
// they can be observed doing their job under this list.
TEST(Verilog1995KeywordSimulation, ForceAndReleaseRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    v = 8'd1;\n"
      "    force v = 8'd43;\n"
      "    #1 result = v;\n"
      "    release v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
