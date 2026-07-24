#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1364-2005" region and drives the
// whole pipeline over it -- preprocess, parse, elaborate, lower, simulate --
// returning the final value of `var_name`. The diagnostic check is what keeps
// the result meaningful: source this version's list admits has to run clean,
// not merely produce a number after the front end recovered from something it
// rejected.
uint64_t RunVerilog2005(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The word this version adds, doing its job at runtime. Reserving it is what
// lets it name a net type, and a net type is only fully observed once a value
// travels through it: the scalar net gates the addition and the vector net
// carries the arithmetic, so the result cannot come out right unless both were
// really built and really driven.
TEST(Verilog2005KeywordSimulation, AddedWordCarriesValuesAtRuntime) {
  auto result = RunVerilog2005(
      "module m;\n"
      "  reg  [7:0] src;\n"
      "  reg        en;\n"
      "  uwire [7:0] bus;\n"
      "  uwire       flag;\n"
      "  reg  [7:0] result;\n"
      "  assign bus  = src + 8'd1;\n"
      "  assign flag = en;\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    en  = 1'b1;\n"
      "    #1 result = flag ? bus + bus - 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The bus holds 22, doubled and less one is 43, and the flag lets it through.
  EXPECT_EQ(result, 43u);
}

// The same net type on a module port, so the addition is observed carrying a
// value between design elements rather than inside one. The child's output port
// is declared with the word this version adds and the parent reads it back
// through a net of that type, so the number arriving at the top could not have
// got there unless the port and the net were both built from it.
TEST(Verilog2005KeywordSimulation, AddedWordTypesAPortAtRuntime) {
  auto result = RunVerilog2005(
      "module child (input wire [7:0] a, output uwire [7:0] y);\n"
      "  assign y = a + a;\n"
      "endmodule\n"
      "module top;\n"
      "  reg   [7:0] src;\n"
      "  uwire [7:0] dst;\n"
      "  reg   [7:0] result;\n"
      "  child u1 (.a(src), .y(dst));\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = dst + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The declaration forms the two tests above do not reach, driven to a value. A
// net declaration may carry its own assignment, and a port may be declared in
// the separate style where the header lists only names and the body supplies
// direction and type. Each is a production of its own, and a number coming out
// the far end is what shows the net the added word opens was really built and
// really driven from that form.
TEST(Verilog2005KeywordSimulation,
     AddedWordTypesEveryDeclarationFormAtRuntime) {
  auto with_assignment = RunVerilog2005(
      "module m;\n"
      "  reg   [7:0] src;\n"
      "  uwire [7:0] bus = src + 8'd1;\n"
      "  reg   [7:0] result;\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = bus + bus - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The declaration's own assignment leaves 22 on the net.
  EXPECT_EQ(with_assignment, 43u);

  auto non_ansi = RunVerilog2005(
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  uwire  [7:0] y;\n"
      "  assign y = a + a;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] src;\n"
      "  wire [7:0] dst;\n"
      "  reg  [7:0] result;\n"
      "  ch u1 (src, dst);\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = dst + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(non_ansi, 43u);
}

// The first included list driven end to end from its own syntax. Inclusion is
// not only about what a word may no longer name: the gate primitives have to go
// on building structure, the resolved net type has to go on combining two
// drivers, and the procedural statements have to go on driving control flow --
// all under a region opened for this version. Reading a value back off a run is
// what shows the inclusion survives the whole pipeline rather than only the
// keyword table.
TEST(Verilog2005KeywordSimulation, IncludedVerilog1995RolesStillRun) {
  auto gates = RunVerilog2005(
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

  auto control = RunVerilog2005(
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

// The second included list at runtime. `automatic` is the entry whose whole
// point is a runtime one -- each call needs storage of its own, which only a
// recursive call shows -- and the loop bound it works against is a
// `localparam`. Both the factorial and the task's accumulation have to survive
// re-entry for this number to come out.
TEST(Verilog2005KeywordSimulation, IncludedAutomaticAndLocalparamStillRun) {
  auto result = RunVerilog2005(
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

// The other pair the second list contributes, and one that only arithmetic can
// separate: both declarations hold the same eight bits, and the comparison
// against zero is what tells them apart. A run in which either word had failed
// to be reserved cannot reach this value.
TEST(Verilog2005KeywordSimulation, IncludedSignedAndUnsignedStillDiverge) {
  auto result = RunVerilog2005(
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

// The constant forms this list admits, each reaching the run as an operand. A
// literal and a `parameter` come from the first included list; a `localparam`
// and the `automatic` that lets a constant function be written come from the
// second. Nothing this version adds itself is needed for any of them, which is
// the point: what it includes is what makes them writable.
TEST(Verilog2005KeywordSimulation, ConstantFormsCarryValuesAtRuntime) {
  auto from_literal = RunVerilog2005(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunVerilog2005(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunVerilog2005(
      "module m;\n"
      "  localparam L = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);

  auto from_function = RunVerilog2005(
      "module m;\n"
      "  function automatic [7:0] twice(input reg [7:0] n);\n"
      "    twice = n + n;\n"
      "  endfunction\n"
      "  reg [7:0] result;\n"
      "  initial result = twice(8'd21) + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_function, 43u);
}

// The same constant forms sizing a declaration rather than standing in an
// expression -- the position where a constant expression is actually required,
// and a different path into the running design. Each variable is four bits wide
// and is handed a value too large for it, so the truncation is what proves the
// width really came from the constant.
TEST(Verilog2005KeywordSimulation, ConstantFormsSizeDeclarationsAtRuntime) {
  const char* kSrc =
      "module m;\n"
      "  parameter  P = 4;\n"
      "  localparam L = 4;\n"
      "  function automatic integer width_of(input reg [7:0] n);\n"
      "    width_of = n;\n"
      "  endfunction\n"
      "  reg [3:0]              from_literal;\n"
      "  reg [P-1:0]            from_parameter;\n"
      "  reg [L-1:0]            from_localparam;\n"
      "  reg [width_of(4)-1:0]  from_function;\n"
      "  reg [7:0]              result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    from_function   = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam - 8'd10;\n"
      "  end\n"
      "endmodule\n";

  // 0x1B truncated to four bits is 11, and three of them less ten is 23.
  EXPECT_EQ(RunVerilog2005(kSrc, "result"), 23u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_function"), 11u);
}

// The negative the three tables imply, carried all the way to a run: a word
// none of them lists is an ordinary identifier under this version, so it can
// name storage that really holds a value, however firmly a later standard
// reserves it.
//
// `interface` is deliberately not among the words here. The preprocessor tracks
// where a design element begins by looking at the first word of a line, and it
// does so without regard to which reserved word list is in force, so a
// statement starting with that word is counted as opening one and the region's
// closing directive is then reported as being inside it. That is the region
// machinery's behaviour rather than anything about this version's list, and the
// word is observed naming things at the parser and elaborator stages instead.
TEST(Verilog2005KeywordSimulation, UnlistedWordsRunAsIdentifiers) {
  auto result = RunVerilog2005(
      "module m;\n"
      "  reg [7:0] logic;\n"
      "  reg [7:0] bit;\n"
      "  reg [7:0] byte;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    logic  = 8'd21;\n"
      "    bit    = 8'd1;\n"
      "    byte   = 8'd0;\n"
      "    result = logic * 2 + bit + byte;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
