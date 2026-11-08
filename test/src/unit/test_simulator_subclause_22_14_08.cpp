#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

uint64_t RunSystemVerilog2012(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1800-2012", body, var_name);
}

uint64_t RunIncludedLists(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1800-2009", body, var_name);
}

uint64_t RunNoconfigList(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1364-2001-noconfig", body, var_name);
}

TEST(SystemVerilog2012KeywordSimulation, AddedImplementsDispatchesAtRuntime) {
  auto direct = RunSystemVerilog2012(
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class port_t implements reader, writer;\n"
      "  int held;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  port_t obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    obj.write(21);\n"
      "    result = obj.read() + obj.read() + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(direct, 43u);

  auto through_interface = RunSystemVerilog2012(
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "class port_t implements reader;\n"
      "  int held;\n"
      "  virtual function int read(); return held + 43; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  reader handle;\n"
      "  port_t obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    handle = obj;\n"
      "    result = handle.read();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(through_interface, 43u);
}

TEST(SystemVerilog2012KeywordSimulation, AddedNettypeNetsCarryValuesAtRuntime) {
  auto through_binding = RunSystemVerilog2012(
      "module m;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net    bn;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  assign bn = src + 8'd1;\n"
      "  initial begin\n"
      "    src = 8'd42;\n"
      "    #1 result = bn;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(through_binding, 43u);

  auto without_binding = RunSystemVerilog2012(
      "module m;\n"
      "  wire        plain;\n"
      "  logic [7:0] result;\n"
      "  assign plain = 8'd43;\n"
      "  initial #1 result = plain;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(without_binding, 1u);

  auto chained = RunSystemVerilog2012(
      "module m;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype byte_net    alias_net;\n"
      "  byte_net    first;\n"
      "  alias_net   second;\n"
      "  logic [7:0] result;\n"
      "  assign first  = 8'd21;\n"
      "  assign second = first + 8'd1;\n"
      "  initial #1 result = first + second;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(chained, 43u);
}

TEST(SystemVerilog2012KeywordSimulation, AddedSoftUnionOverlaysStorage) {
  auto overlaid = RunSystemVerilog2012(
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  overlay_t   u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u.a = 8'd43;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(overlaid, 43u);

  auto reversed = RunSystemVerilog2012(
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  overlay_t   u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u.b = 8'd21;\n"
      "    result = u.a + u.b + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(reversed, 43u);
}

TEST(SystemVerilog2012KeywordSimulation,
     AddedSoftConstraintsSteerRandomization) {
  const std::string kPreferred =
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v == 43; v >= 0; v < 100; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  c obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    void'(obj.randomize());\n"
      "    result = obj.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunSystemVerilog2012(kPreferred, "result"), 43u);

  auto later_wins = RunSystemVerilog2012(
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v == 21; soft v == 43; v >= 0; v < 100; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  c obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    void'(obj.randomize());\n"
      "    result = obj.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(later_wins, 43u);

  auto hard_wins = RunSystemVerilog2012(
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v == 43; v == 21; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  c obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    void'(obj.randomize());\n"
      "    result = obj.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(hard_wins, 21u);

  auto discarded = RunSystemVerilog2012(
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v == 43; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  c obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    void'(obj.randomize() with { disable soft v; v == 7; });\n"
      "    result = obj.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(discarded, 7u);
}

TEST(SystemVerilog2012KeywordSimulation, AddedSoftDistributionSteersSolver) {
  const std::string kSrc =
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v dist {43 := 1}; v >= 0; v < 100; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  c obj;\n"
      "  initial begin\n"
      "    obj = new();\n"
      "    void'(obj.randomize());\n"
      "    result = obj.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "result"), 43u);
}

TEST(SystemVerilog2012KeywordSimulation, AddedSoftUnionNeedsNoTypedef) {
  auto overlaid = RunSystemVerilog2012(
      "module m;\n"
      "  union soft { logic [7:0] a; logic [7:0] b; } u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u.a = 8'd43;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(overlaid, 43u);
}

TEST(SystemVerilog2012KeywordSimulation, AddedNettypeCrossesAPackageBoundary) {
  auto result = RunSystemVerilog2012(
      "package pkg;\n"
      "  nettype logic [7:0] byte_net;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_net    bn;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  assign bn = src + 8'd1;\n"
      "  initial begin\n"
      "    src = 8'd42;\n"
      "    #1 result = bn;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(SystemVerilog2012KeywordSimulation,
     AddedWordsNameStorageUnderIncludedLists) {
  const char* const kSrc =
      "module m;\n"
      "  reg [7:0] implements   = 8'd7;\n"
      "  reg [7:0] interconnect = 8'd9;\n"
      "  reg [7:0] nettype      = 8'd11;\n"
      "  reg [7:0] soft         = 8'd16;\n"
      "  reg [7:0] result;\n"
      "  initial result = implements + interconnect + nettype + soft;\n"
      "endmodule\n";
  EXPECT_EQ(RunIncludedLists(kSrc, "result"), 43u);

  EXPECT_EQ(RunIncludedLists(kSrc, "implements"), 7u);
  EXPECT_EQ(RunIncludedLists(kSrc, "interconnect"), 9u);
  EXPECT_EQ(RunIncludedLists(kSrc, "nettype"), 11u);
  EXPECT_EQ(RunIncludedLists(kSrc, "soft"), 16u);
}

TEST(SystemVerilog2012KeywordSimulation, IncludedVerilog1995RolesStillRun) {
  auto gates = RunSystemVerilog2012(
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

  auto control = RunSystemVerilog2012(
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

TEST(SystemVerilog2012KeywordSimulation, IncludedVerilog2001RolesStillRun) {
  auto result = RunSystemVerilog2012(
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

  auto signedness = RunSystemVerilog2012(
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

TEST(SystemVerilog2012KeywordSimulation,
     ConfigurationWordsNameStorageUnderTheNoconfigList) {
  auto result = RunNoconfigList(
      "module m;\n"
      "  reg [7:0] cell      = 8'd34;\n"
      "  reg [7:0] config    = 8'd1;\n"
      "  reg [7:0] design    = 8'd1;\n"
      "  reg [7:0] endconfig = 8'd1;\n"
      "  reg [7:0] incdir    = 8'd1;\n"
      "  reg [7:0] include   = 8'd1;\n"
      "  reg [7:0] instance  = 8'd1;\n"
      "  reg [7:0] liblist   = 8'd1;\n"
      "  reg [7:0] library   = 8'd1;\n"
      "  reg [7:0] use       = 8'd1;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = cell + config + design + endconfig;\n"
      "    result = result + incdir + include + instance;\n"
      "    result = result + liblist + library + use;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(SystemVerilog2012KeywordSimulation, IncludedVerilog2005RoleStillRuns) {
  auto result = RunSystemVerilog2012(
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

TEST(SystemVerilog2012KeywordSimulation,
     IncludedSystemVerilog2005RolesStillRun) {
  auto types = RunSystemVerilog2012(
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
  EXPECT_EQ(types, 43u);

  auto user_types = RunSystemVerilog2012(
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
  EXPECT_EQ(user_types, 43u);

  auto statements = RunSystemVerilog2012(
      "module m;\n"
      "  int slots [0:3];\n"
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
      "    slots[0] = 1; slots[1] = 1; slots[2] = 1; slots[3] = 1;\n"
      "    foreach (slots[j]) total = total + slots[j];\n"
      "    sel = 2'b01;\n"
      "    unique case (sel) 2'b01: total = total + 3; default: total = 0;\n"
      "    endcase\n"
      "    if (sel inside {2'b01, 2'b10}) total = total + twice(6);\n"
      "    result = total;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(statements, 41u);

  auto processes = RunSystemVerilog2012(
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
  EXPECT_EQ(processes, 44u);
}

TEST(SystemVerilog2012KeywordSimulation,
     IncludedSystemVerilog2009RolesStillRun) {
  auto substituted = RunSystemVerilog2012(
      "let gain = 20;\n"
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] result;\n"
      "  let sum(untyped x, untyped y) = x + y;\n"
      "  initial begin\n"
      "    a = 8'd21;\n"
      "    b = 8'd1;\n"
      "    result = sum(a, b) + gain + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(substituted, 43u);

  auto qualified = RunSystemVerilog2012(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic       flag;\n"
      "  logic [7:0] total;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    sel   = 2'b01;\n"
      "    flag  = 1'b1;\n"
      "    unique0 case (sel) 2'b01: total = total + 8'd20; 2'b10: total = 0;\n"
      "    endcase\n"
      "    sel = 2'b10;\n"
      "    unique0 casez (sel) 2'b1?: total = total + 8'd12; default: total = "
      "0;\n"
      "    endcase\n"
      "    unique0 if (flag) total = total + 8'd11; else total = 8'd0;\n"
      "    result = total;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(qualified, 43u);

  auto no_match = RunSystemVerilog2012(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd43;\n"
      "    sel    = 2'b11;\n"
      "    unique0 case (sel) 2'b01: result = 8'd0; 2'b10: result = 8'd1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(no_match, 43u);
}

TEST(SystemVerilog2012KeywordSimulation, ConstantFormsCarryValuesAtRuntime) {
  auto from_literal = RunSystemVerilog2012(
      "module m;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunSystemVerilog2012(
      "module m;\n"
      "  parameter P = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunSystemVerilog2012(
      "module m;\n"
      "  localparam L = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);

  auto from_function = RunSystemVerilog2012(
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

TEST(SystemVerilog2012KeywordSimulation,
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

  EXPECT_EQ(RunSystemVerilog2012(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_function"), 11u);
}

TEST(SystemVerilog2012KeywordSimulation,
     WordsOutsideTheTablesRunAsIdentifiers) {
  auto result = RunSystemVerilog2012(
      "module m;\n"
      "  logic [7:0] implement;\n"
      "  logic [7:0] interconnects;\n"
      "  logic [7:0] nettypes;\n"
      "  logic [7:0] softly;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    implement     = 8'd21;\n"
      "    interconnects = 8'd1;\n"
      "    nettypes      = 8'd0;\n"
      "    softly        = 8'd0;\n"
      "    result = implement * 2 + interconnects + nettypes + softly;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
