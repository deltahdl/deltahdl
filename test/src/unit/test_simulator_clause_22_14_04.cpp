#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1364-2001-noconfig" region and runs
// the whole pipeline over it -- preprocess, parse, elaborate, lower,
// simulate -- returning the final value of `var_name`. The diagnostic check is
// what keeps the result meaningful: source this version's list admits has to
// run clean, not merely produce a number after the front end recovered from
// something it rejected.
uint64_t RunNoconfig(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid =
      f.mgr.AddFile("<test>", "`begin_keywords \"1364-2001-noconfig\"\n" +
                                  body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The exception at runtime. Being dropped from the reserved list has to mean
// the word carries a value like any other name, so this spreads all ten across
// a hierarchy: the child module's name, both its port names, its parameter,
// and in the parent a variable, a net, a second variable, the instance name, a
// task, and a named block. The value the child computes has to reach the
// parent for the run to produce this result, so every one of the ten had to
// resolve -- getting past the parser would not be enough.
TEST(NoconfigKeywordSimulation, ExcludedWordsRunAcrossAHierarchy) {
  auto result = RunNoconfig(
      "module cell (input wire [7:0] design, output wire [7:0] library);\n"
      "  parameter incdir = 2;\n"
      "  assign library = design * incdir;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] instance;\n"
      "  wire [7:0] liblist;\n"
      "  reg  [7:0] endconfig;\n"
      "  reg  [7:0] result;\n"
      "  cell config (.design(instance), .library(liblist));\n"
      "  task use; begin result = liblist + endconfig; end endtask\n"
      "  initial begin : include\n"
      "    instance = 8'd21;\n"
      "    endconfig = 8'd1;\n"
      "    #1 use;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The child doubles 21 and the task adds the one the parent held.
  EXPECT_EQ(result, 43u);
}

// A dropped word naming an event, triggered with `->` and waited on by an
// `always` procedure. The run observes both sides of the rule at once: an
// inherited keyword still opens the declaration, and the dropped word still
// names it and carries the trigger through to the waiting process.
TEST(NoconfigKeywordSimulation, ExcludedWordNamesEventDrivingAProcess) {
  auto result = RunNoconfig(
      "module m;\n"
      "  event design;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    #1 -> design;\n"
      "  end\n"
      "  always @(design) result = result + 8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The constant forms this version admits, each carried by one of the ten
// dropped words and each reaching the run by a different path. A `parameter`
// is inherited from Table 22-1 and a `localparam` is an addition this version
// keeps, so the declaration keywords are on the reserved side of the rule
// while every name they introduce is on the dropped side.
TEST(NoconfigKeywordSimulation, ExcludedWordsCarryConstantsAtRuntime) {
  auto from_literal = RunNoconfig(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunNoconfig(
      "module m;\n"
      "  parameter incdir = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = incdir * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunNoconfig(
      "module m;\n"
      "  localparam liblist = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = liblist * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);
}

// The same constant forms sizing a declaration rather than standing in an
// expression -- a different path into the running design. Each variable is
// four bits wide and is handed a value too large for it, so the truncation is
// what proves the width really came from the constant the dropped word names.
TEST(NoconfigKeywordSimulation, ExcludedWordConstantsSizeADeclaration) {
  const char* kSrc =
      "module m;\n"
      "  parameter  incdir  = 4;\n"
      "  localparam liblist = 4;\n"
      "  reg [3:0]          from_literal;\n"
      "  reg [incdir-1:0]   from_parameter;\n"
      "  reg [liblist-1:0]  from_localparam;\n"
      "  reg [7:0]          result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam + 8'd10;\n"
      "  end\n"
      "endmodule\n";

  // 0x1B truncated to four bits is 11, and three of them plus ten is 43.
  EXPECT_EQ(RunNoconfig(kSrc, "result"), 43u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_localparam"), 11u);
}

// Behaving as "1364-2001" does, observed at runtime: `automatic` is an
// addition this version keeps, and its whole point is a runtime one -- each
// call needs its own copy of the subroutine's storage, which only a recursive
// call can show. The factorial and the task's accumulation both have to
// survive re-entry for this number to come out, and the loop bound is a
// `localparam`, another addition this version keeps.
TEST(NoconfigKeywordSimulation, KeptAutomaticAndLocalparamStillRun) {
  auto result = RunNoconfig(
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

// `signed` and `unsigned` are additions this version keeps, and what they
// select is only visible once arithmetic runs. The two declarations hold the
// same eight bits; the comparison against zero is what separates them, so a
// run in which either word had been dropped along with the other ten cannot
// reach this value.
TEST(NoconfigKeywordSimulation, KeptSignedAndUnsignedStillDiverge) {
  auto result = RunNoconfig(
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

// A dropped word naming a subroutine's formal argument, driven to a value. The
// parser sees the name in the header; only a run shows an argument actually
// carrying a value into the body and back out, which is a different thing for
// a function returning a result than for a task writing through to a variable.
// Both are exercised here, chained so the task consumes what the function
// produced.
TEST(NoconfigKeywordSimulation, ExcludedWordNamesASubroutineArgumentAtRuntime) {
  auto result = RunNoconfig(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  function [7:0] twice(input reg [7:0] library);\n"
      "    twice = library + library;\n"
      "  endfunction\n"
      "  task bump(input reg [7:0] incdir);\n"
      "    result = result + incdir;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = 8'd3;\n"
      "    bump(twice(8'd20));\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The function doubles 20 and the task adds it to the 3 already held.
  EXPECT_EQ(result, 43u);
}

// The inherited list driven end to end from its own syntax. The exception this
// subclause names reaches Table 22-2 only, so the words the earlier list
// contributes have to go on doing their real work under this version: the gate
// primitives build structure, the resolved net type combines two drivers, and
// the procedural statements drive actual control flow. Reading a value back off
// a run is what shows the inheritance survives the whole pipeline rather than
// only the keyword table.
TEST(NoconfigKeywordSimulation, InheritedKeywordRolesStillRun) {
  auto gates = RunNoconfig(
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
  // and(1,1) is 1, nor(1,1) is 0, and a wand resolving two ones is 1.
  EXPECT_EQ(gates, 5u);

  auto control = RunNoconfig(
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
  // Twenty from the for loop, ten from the repeat, two from the while, and one
  // from the matching casez branch.
  EXPECT_EQ(control, 33u);
}

// Words neither table lists stay ordinary identifiers under this version too:
// the exception adds ten names to that group without disturbing it. Here a
// word a later standard reserves names the variable that carries the result.
TEST(NoconfigKeywordSimulation, UnlistedWordsStillRunAsIdentifiers) {
  auto result = RunNoconfig(
      "module m;\n"
      "  reg [7:0] logic;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    logic = 8'd21;\n"
      "    result = logic * 2 + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
