#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1800-2005" region and drives the
// whole pipeline over it -- preprocess, parse, elaborate, lower, simulate --
// returning the final value of `var_name`. The diagnostic check is what keeps
// the result meaningful: source this version's list admits has to run clean,
// not merely produce a number after the front end recovered from something it
// rejected.
uint64_t RunSystemVerilog2005(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2005\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The data types this version adds, doing their job at runtime. Reserving the
// words is what lets them name types, and a type is only fully observed once a
// value travels through one: each declaration is handed a number and the total
// comes back out, so none of them can be right unless every declaration was
// really built with the width it asked for.
TEST(SystemVerilog2005KeywordSimulation, AddedTypeWordsCarryValuesAtRuntime) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  logic    [7:0] as_logic;\n"
      "  bit      [7:0] as_bit;\n"
      "  byte           as_byte;\n"
      "  shortint       as_shortint;\n"
      "  int            as_int;\n"
      "  longint        as_longint;\n"
      "  var logic [7:0] as_var;\n"
      "  logic    [7:0] result;\n"
      "  initial begin\n"
      "    as_logic    = 8'd20;\n"
      "    as_bit      = 8'd10;\n"
      "    as_shortint = 16'd6;\n"
      "    as_int      = 4;\n"
      "    as_longint  = 2;\n"
      "    as_byte     = 8'd1;\n"
      "    as_var      = 8'd0;\n"
      "    result = as_logic + as_bit + as_shortint + as_int[7:0] +\n"
      "             as_longint[7:0] + as_byte + as_var;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // 20 + 10 + 6 + 4 + 2 + 1 + 0 = 43.
  EXPECT_EQ(result, 43u);
}

// The truncation each added type imposes, which is the half a sum of small
// numbers would not show: a value too large for the declaration has to be cut
// down to the width the type names. Every one of these is handed the same
// pattern and read back on its own, so a width that came out wrong shows up as
// a wrong number rather than being absorbed into a total.
TEST(SystemVerilog2005KeywordSimulation, AddedTypeWordsSizeTheirStorage) {
  const char* kSrc =
      "module m;\n"
      "  byte     as_byte;\n"
      "  shortint as_shortint;\n"
      "  int      as_int;\n"
      "  bit [3:0] as_nibble;\n"
      "  initial begin\n"
      "    as_byte     = 32'h0000_1234;\n"
      "    as_shortint = 32'h0012_3456;\n"
      "    as_int      = 64'h0000_0001_1234_5678;\n"
      "    as_nibble   = 8'h5B;\n"
      "  end\n"
      "endmodule\n";

  EXPECT_EQ(RunSystemVerilog2005(kSrc, "as_byte"), 0x34u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "as_shortint"), 0x3456u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "as_int"), 0x12345678u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "as_nibble"), 0xBu);
}

// The same wrapper for "1364-2005", the union of the three lists this version
// includes. It is what the added words are measured against: source that runs
// here and cannot be written under this version's list is source the addition
// took away, and source that runs only under this version's list is what the
// addition bought.
uint64_t RunIncludedLists(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The declaration forms the two tests above do not reach, driven to a value. A
// declaration may carry its own initializer, a port may be typed in the module
// header, and a port may instead be typed in the body in the separate style.
// Each is a production of its own, and a number arriving at the top is what
// shows the object the added word typed was really built and really driven
// from that form -- here across a module boundary rather than inside one.
TEST(SystemVerilog2005KeywordSimulation,
     AddedTypeWordsTypeEveryDeclarationFormAtRuntime) {
  auto ansi_ports = RunSystemVerilog2005(
      "module child (input logic [7:0] a, input byte b, output int y);\n"
      "  assign y = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  byte        step;\n"
      "  int         dst;\n"
      "  int         counted = 20;\n"
      "  logic [7:0] result;\n"
      "  child u1 (.a(src), .b(step), .y(dst));\n"
      "  initial begin\n"
      "    src  = 8'd21;\n"
      "    step = 8'd1;\n"
      "    #1 result = dst[7:0] + counted[7:0] + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The child adds 21 and 1 into its int output; the parent's initialized
  // declaration contributes 20, and one more makes 43.
  EXPECT_EQ(ansi_ports, 43u);

  auto non_ansi = RunSystemVerilog2005(
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  logic  [7:0] y;\n"
      "  always_comb y = a + a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  logic [7:0] result;\n"
      "  ch u1 (src, dst);\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = dst + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(non_ansi, 43u);
}

// The other side of the addition, carried to a run. Every test above shows an
// added word doing its keyword job under this version; this one shows the very
// same words naming storage that really holds a value under "1364-2005", the
// union of everything this version includes. Without this leg the runtime
// evidence would be consistent with the words having been reserved all along
// rather than added by this version_specifier.
TEST(SystemVerilog2005KeywordSimulation,
     AddedWordsNameStorageUnderIncludedLists) {
  auto result = RunIncludedLists(
      "module m;\n"
      "  reg [7:0] logic;\n"
      "  reg [7:0] int;\n"
      "  reg [7:0] byte;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    logic  = 8'd21;\n"
      "    int    = 8'd1;\n"
      "    byte   = 8'd0;\n"
      "    result = logic * 2 + int + byte;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The statement words this version adds, driving real control flow. The
// do-while runs its body before testing, the loop-control words cut two of the
// four passes short, the case qualifiers pick a branch, the set membership test
// picks another, and the function returns through the added `return` -- so the
// number that comes out depends on every one of them behaving as its keyword
// says rather than merely parsing.
TEST(SystemVerilog2005KeywordSimulation,
     AddedStatementWordsDriveControlFlowAtRuntime) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  int i;\n"
      "  int total;\n"
      "  logic [1:0] sel;\n"
      "  int result;\n"
      "  function int twice(input int n);\n"
      "    return n + n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    do total = total + 10; while (total < 20);\n"
      "    for (i = 0; i < 4; i = i + 1) begin\n"
      "      if (i == 1) continue;\n"
      "      if (i == 3) break;\n"
      "      total = total + 1;\n"
      "    end\n"
      "    sel = 2'b01;\n"
      "    unique case (sel) 2'b01: total = total + 3; default: total = 0;\n"
      "    endcase\n"
      "    priority case (sel) 2'b01: total = total + 4; default: total = 0;\n"
      "    endcase\n"
      "    if (sel inside {2'b01, 2'b10}) total = total + twice(6);\n"
      "    result = total;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // Two do-while passes give 20; the for loop adds one on i=0 and one on i=2
  // (i=1 continues, i=3 breaks) for 22; the two case branches make 29; and the
  // membership test adds twice(6) for 41.
  EXPECT_EQ(result, 41u);
}

// The word that iterates an array, which is the one added statement with no
// counterpart in the lists this version includes: it takes its bounds from the
// array rather than from an expression the source writes out. Each element is
// given a value and the loop sums them, so the total can only come out right if
// the loop really visited every element.
TEST(SystemVerilog2005KeywordSimulation, AddedForeachWalksAnArrayAtRuntime) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  int slots [0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    slots[0] = 20;\n"
      "    slots[1] = 10;\n"
      "    slots[2] = 8;\n"
      "    slots[3] = 5;\n"
      "    result = 0;\n"
      "    foreach (slots[j]) result = result + slots[j];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

// The words that open a process, run rather than merely built. The inferred
// combinational block has to recompute when its input changes and the inferred
// sequential block has to sample on the clock edge, so the value read at the
// end could not be reached by either block running once or not at all.
TEST(SystemVerilog2005KeywordSimulation, AddedProcessWordsRunAtRuntime) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  logic       clk;\n"
      "  logic [7:0] d;\n"
      "  logic [7:0] combo;\n"
      "  logic [7:0] q;\n"
      "  logic [7:0] result;\n"
      "  always_comb combo = d + 8'd1;\n"
      "  always_ff @(posedge clk) q <= combo;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    d   = 8'd20;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    d = 8'd21;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 result = q + combo;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The second edge latches 22 and the combinational block then holds 22 - the
  // first edge's 21 is overwritten, so a block that never re-ran cannot get
  // here.
  EXPECT_EQ(result, 44u);
}

// The user-defined type words carrying values. A typedef'd vector and an
// enumeration are declared, given values, and read back through arithmetic, so
// the named type has to have reached the run with the width its definition
// gave it and the enumeration's members have to have resolved to the constants
// their declaration order implies.
TEST(SystemVerilog2005KeywordSimulation,
     AddedTypedefAndEnumCarryValuesAtRuntime) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;\n"
      "  byte_t  wide;\n"
      "  state_t phase;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    wide  = 8'd41;\n"
      "    phase = DONE;\n"
      "    result = wide + phase;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // The third enumeration member stands for 2.
  EXPECT_EQ(result, 43u);
}

// The first included list driven end to end from its own syntax. Inclusion is
// not only about what a word may no longer name: the gate primitives have to go
// on building structure, the resolved net type has to go on combining two
// drivers, and the procedural statements have to go on driving control flow --
// all under a region opened for this version_specifier.
TEST(SystemVerilog2005KeywordSimulation, IncludedVerilog1995RolesStillRun) {
  auto gates = RunSystemVerilog2005(
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

  auto control = RunSystemVerilog2005(
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
// recursive call shows -- and the value it works against is a `localparam`.
// Both the factorial and the task's accumulation have to survive re-entry for
// this number to come out.
TEST(SystemVerilog2005KeywordSimulation, IncludedVerilog2001RolesStillRun) {
  auto result = RunSystemVerilog2005(
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

  auto signedness = RunSystemVerilog2005(
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
  EXPECT_EQ(signedness, 43u);
}

// The third included list at runtime -- one word, and a net type is only fully
// observed once a value travels through it. The scalar net gates the addition
// and the vector net carries it, so the result cannot come out right unless
// both were really built and really driven under this version's list.
TEST(SystemVerilog2005KeywordSimulation, IncludedVerilog2005RoleStillRuns) {
  auto result = RunSystemVerilog2005(
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

// The constant forms this list admits, each reaching the run as an operand. A
// literal and a `parameter` come from the first included list, a `localparam`
// and the `automatic` that lets a constant function be written come from the
// second, and `int` -- the type the function returns and takes -- is one of
// this version's own additions.
TEST(SystemVerilog2005KeywordSimulation, ConstantFormsCarryValuesAtRuntime) {
  auto from_literal = RunSystemVerilog2005(
      "module m;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunSystemVerilog2005(
      "module m;\n"
      "  parameter P = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunSystemVerilog2005(
      "module m;\n"
      "  localparam L = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);

  auto from_function = RunSystemVerilog2005(
      "module m;\n"
      "  function automatic int twice(input int n);\n"
      "    return n + n;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = twice(21) + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_function, 43u);
}

// The fifth constant form -- a genvar -- has no test at this stage, and cannot
// have one. It shows its value in the copies its loop produces rather than in a
// width or an operand, so observing it at runtime means giving each pass of the
// loop something to drive and reading the results back after a run. Nothing a
// loop generate construct produces reaches a running design here: the same
// array driven by four plain continuous assignments reads back correctly while
// the generated form reads zero, and that holds with no `begin_keywords region
// at all and with none of this version's added types in the source. The fault
// is in how the construct is lowered, not in which words are reserved, so no
// test here can drive it. The genvar is observed instead at the elaborator,
// where the copies really are produced -- one declaration per iteration, with a
// nested condition singling out a single pass, so the genvar is seen holding a
// different constant each time round.
//
// A parameter declaration is a syntactic position of its own for the added type
// words, and the one that puts them on the constant-expression axis. Both the
// overridable and the local form are here, each spent twice over -- once as a
// plain operand and once as the width of a declaration that is then handed a
// value too large for it, so the truncation shows the constant really reached
// the declaration rather than only the expression.
TEST(SystemVerilog2005KeywordSimulation,
     AddedTypeWordsQualifyConstantsAtRuntime) {
  const char* kSrc =
      "module m;\n"
      "  parameter  int  P = 21;\n"
      "  localparam byte S = 8'd4;\n"
      "  logic [S-1:0] sized_by_localparam;\n"
      "  logic [7:0]   result;\n"
      "  initial begin\n"
      "    sized_by_localparam = 8'h1B;\n"
      "    result = P[7:0] * 2 + 8'd1;\n"
      "  end\n"
      "endmodule\n";

  EXPECT_EQ(RunSystemVerilog2005(kSrc, "result"), 43u);
  // 0x1B cut down to the four bits the typed localparam asked for is 11.
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "sized_by_localparam"), 11u);
}

// The same constant forms sizing a declaration rather than standing in an
// expression -- the position where a constant expression is actually required,
// and a different path into the running design. Each variable is four bits wide
// and is handed a value too large for it, so the truncation is what proves the
// width really came from the constant.
TEST(SystemVerilog2005KeywordSimulation,
     ConstantFormsSizeDeclarationsAtRuntime) {
  const char* kSrc =
      "module m;\n"
      "  parameter  P = 4;\n"
      "  localparam L = 4;\n"
      "  function automatic int width_of(input int n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  logic [3:0]              from_literal;\n"
      "  logic [P-1:0]            from_parameter;\n"
      "  logic [L-1:0]            from_localparam;\n"
      "  logic [width_of(4)-1:0]  from_function;\n"
      "  logic [7:0]              result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    from_function   = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam - 8'd10;\n"
      "  end\n"
      "endmodule\n";

  // 0x1B truncated to four bits is 11, and three of them less ten is 23.
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_function"), 11u);
}

// The negative the four tables imply, carried all the way to a run: a word none
// of them lists is an ordinary identifier under this version, so it can name
// storage that really holds a value, however firmly a later standard reserves
// it. None of the words used here opens a design element, which keeps the
// region machinery -- it tracks design elements by a line's first word, without
// regard to the list in force -- out of the way of the statements below.
TEST(SystemVerilog2005KeywordSimulation, LaterWordsRunAsIdentifiers) {
  auto result = RunSystemVerilog2005(
      "module m;\n"
      "  logic [7:0] until;\n"
      "  logic [7:0] let;\n"
      "  logic [7:0] global;\n"
      "  logic [7:0] soft;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    until  = 8'd21;\n"
      "    let    = 8'd1;\n"
      "    global = 8'd0;\n"
      "    soft   = 8'd0;\n"
      "    result = until * 2 + let + global + soft;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
