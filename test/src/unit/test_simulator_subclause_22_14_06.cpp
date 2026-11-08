#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(result, 43u);
}

TEST(SystemVerilog2005KeywordSimulation, AddedTypeWordsSizeTheirStorage) {
  const char* const kSrc =
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

TEST(SystemVerilog2005KeywordSimulation,
     AddedTypeWordsTypeEveryDeclarationFormAtRuntime) {
  auto ansi_ports = RunSystemVerilog2005(
      "module child (input logic [7:0] a, input var byte b, output int y);\n"
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
  EXPECT_EQ(result, 41u);
}

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
  EXPECT_EQ(result, 44u);
}

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
  EXPECT_EQ(result, 43u);
}

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
  EXPECT_EQ(control, 33u);
}

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
  EXPECT_EQ(signedness, 43u);
}

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
  EXPECT_EQ(result, 43u);
}

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

TEST(SystemVerilog2005KeywordSimulation,
     AddedTypeWordsQualifyConstantsAtRuntime) {
  const char* const kSrc =
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
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "sized_by_localparam"), 11u);
}

TEST(SystemVerilog2005KeywordSimulation,
     ConstantFormsSizeDeclarationsAtRuntime) {
  const char* const kSrc =
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

  EXPECT_EQ(RunSystemVerilog2005(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2005(kSrc, "from_function"), 11u);
}

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
