#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1364-2001" region and runs the whole
// pipeline over it -- preprocess, parse, elaborate, lower, simulate --
// returning the final value of `var_name`. The diagnostic check is what keeps
// the result meaningful: source this version's list admits has to run clean,
// not merely produce a number after the front end recovered from something it
// rejected.
uint64_t Run2001(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// `localparam` is an addition of this version, and a constant it declares has
// to be worth something at runtime, not merely parse. The three constant forms
// this list makes available in an expression -- a literal, a `parameter`
// carried over from the earlier list, and a `localparam` this version adds --
// all reach the same value.
TEST(Verilog2001KeywordSimulation, LiteralParameterAndLocalparamAgree) {
  auto from_literal = Run2001(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = Run2001(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = Run2001(
      "module m;\n"
      "  localparam L = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);
}

// `automatic` is an addition of this version whose whole point is a runtime
// one: each call needs its own copy of the subroutine's storage, which only a
// recursive call can show. The factorial and the task's accumulation both have
// to survive re-entry for this number to come out.
TEST(Verilog2001KeywordSimulation, AutomaticFunctionAndTaskRun) {
  auto result = Run2001(
      "module m;\n"
      "  localparam L = 20;\n"
      "  reg [7:0] result;\n"
      "  function automatic [7:0] fact(input reg [7:0] n);\n"
      "    begin\n"
      "      if (n <= 1) fact = 8'd1;\n"
      "      else fact = n * fact(n - 1);\n"
      "    end\n"
      "  endfunction\n"
      "  task automatic bump(input reg [7:0] d);\n"
      "    result = result + d;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = L;\n"
      "    bump(fact(8'd3));\n"
      "    bump(8'd17);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // 20 + 3! + 17 = 43.
  EXPECT_EQ(result, 43u);
}

// `signed` is an addition of this version, and what it selects is only visible
// once arithmetic runs: the same bit patterns multiplied as signed values give
// a different answer than they would unsigned, and the negation below can only
// land on this value if both operands were treated as signed.
TEST(Verilog2001KeywordSimulation, SignedDeclarationsChangeTheArithmetic) {
  auto result = Run2001(
      "module m;\n"
      "  reg signed [7:0] a, b;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    a = -8'sd7;\n"
      "    b = 8'sd6;\n"
      "    result = -(a * b) + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// `unsigned` is the other half of that addition, and the only way to tell it
// apart from `signed` is to run both. The two declarations hold the same eight
// bits; the comparison against zero is what separates them, so a run in which
// `unsigned` had been ignored -- or in which neither word was a keyword --
// cannot reach this value.
TEST(Verilog2001KeywordSimulation, SignedAndUnsignedDeclarationsDiverge) {
  auto result = Run2001(
      "module m;\n"
      "  reg signed   [7:0] s;\n"
      "  reg unsigned [7:0] u;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    s = 8'hF8;\n"
      "    u = 8'hF8;\n"
      "    result = (s < 0 ? 8'd40 : 8'd0) + (u < 8'd1 ? 8'd0 : 8'd3);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The signed copy reads as negative and the unsigned copy does not.
  EXPECT_EQ(result, 43u);
}

// The same addition in the other declaration position it qualifies: a net
// rather than a variable. Nets and variables take different paths from the
// declaration into the running design, so the keyword has to survive both, and
// only a run can show that the value arriving over the net is still read as
// signed.
TEST(Verilog2001KeywordSimulation, SignedNetKeepsItsSignednessAtRuntime) {
  auto result = Run2001(
      "module m;\n"
      "  reg  signed [7:0] d;\n"
      "  wire signed [7:0] w;\n"
      "  reg  [7:0] result;\n"
      "  assign w = d;\n"
      "  initial begin\n"
      "    d = 8'hF8;\n"
      "    #1 result = (w < 0) ? 8'd43 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The constant forms again, but sizing a declaration rather than standing in an
// expression -- a different path into the running design than the operand test
// above takes. Each variable is four bits wide and is handed a value too large
// for it, so the truncation is what proves the width really came from the
// constant. All three forms this list admits have to truncate identically: the
// literal and the `parameter` are inherited, the `localparam` is an addition.
TEST(Verilog2001KeywordSimulation, ConstantFormsAllSizeADeclaration) {
  const char* kSrc =
      "module m;\n"
      "  parameter  P = 4;\n"
      "  localparam L = 4;\n"
      "  reg [3:0]   from_literal;\n"
      "  reg [P-1:0] from_parameter;\n"
      "  reg [L-1:0] from_localparam;\n"
      "  reg [7:0]   result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam + 8'd10;\n"
      "  end\n"
      "endmodule\n";

  // 0x1B truncated to four bits is 11, and three of them plus ten is 43.
  EXPECT_EQ(Run2001(kSrc, "result"), 43u);
  EXPECT_EQ(Run2001(kSrc, "from_literal"), 11u);
  EXPECT_EQ(Run2001(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(Run2001(kSrc, "from_localparam"), 11u);
}

// The inclusion half at runtime: the gate primitives, net types, and
// procedural statements the earlier list names still build working structure
// and drive real control flow under this one.
TEST(Verilog2001KeywordSimulation, InheritedKeywordsStillRun) {
  auto gates = Run2001(
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
  EXPECT_EQ(gates, 5u);

  auto control = Run2001(
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
  EXPECT_EQ(control, 33u);
}

// The inherited event-control words doing their job under this list: an
// `always` procedure sensitive to a `posedge`/`negedge` list joined by `or`,
// with an `if`/`else` pair choosing between them. The count the run leaves
// behind is reachable only if the sensitivity list and both branches were
// understood as keywords.
TEST(Verilog2001KeywordSimulation, InheritedEventControlAndBranchRun) {
  auto result = Run2001(
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

// Words neither table lists are ordinary identifiers under this version, and
// they carry values at runtime like any other name: this spreads them across a
// hierarchy -- the child module's name, its two port names, a parameter, a
// task, a variable, and the instance name are all words later standards
// reserve. The value the child computes has to reach the parent for the run to
// produce this result, so every one of those names had to resolve.
TEST(Verilog2001KeywordSimulation, FreedWordsRunAcrossAHierarchy) {
  auto result = Run2001(
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

// An `event` declared under this list, triggered with `->`, and waited on by
// an `always` procedure. The name carrying the event is a word a later
// standard reserved, so the run observes both sides of the rule at once: the
// inherited keyword still opens a declaration, and the freed word still names
// one.
TEST(Verilog2001KeywordSimulation, FreedWordNamesAnEventDrivingAProcess) {
  auto result = Run2001(
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

}  // namespace
