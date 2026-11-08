#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

uint64_t RunSystemVerilog2009(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1800-2009", body, var_name);
}

uint64_t RunIncludedLists(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1800-2005", body, var_name);
}

uint64_t RunNoconfigList(const std::string& body, const char* var_name) {
  return RunUnderKeywordVersion("1364-2001-noconfig", body, var_name);
}

std::string RunSystemVerilog2009Output(const std::string& body) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2009\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return "";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());

  testing::internal::CaptureStdout();
  f.scheduler.Run();
  return testing::internal::GetCapturedStdout();
}

TEST(SystemVerilog2009KeywordSimulation, AddedLetSubstitutesValuesAtRuntime) {
  auto result = RunSystemVerilog2009(
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
  EXPECT_EQ(result, 43u);

  auto reused = RunSystemVerilog2009(
      "module m;\n"
      "  logic [7:0] result;\n"
      "  let step = 21;\n"
      "  initial result = step + step + 8'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(reused, 43u);
}

TEST(SystemVerilog2009KeywordSimulation,
     AddedUnique0QualifiesBranchesAtRuntime) {
  auto result = RunSystemVerilog2009(
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
  EXPECT_EQ(result, 43u);

  auto no_match = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation, AddedCheckerRunsAtRuntime) {
  auto out = RunSystemVerilog2009Output(
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req)\n"
      "    $display(\"HELD\");\n"
      "  else\n"
      "    $display(\"BROKEN\");\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  handshake u_chk (clk, req);\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    req = 1'b1;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    req = 1'b0;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 $display(\"END\");\n"
      "  end\n"
      "endmodule\n");

  EXPECT_NE(out.find("HELD"), std::string::npos) << out;
  EXPECT_NE(out.find("BROKEN"), std::string::npos) << out;
  EXPECT_NE(out.find("END"), std::string::npos) << out;
  EXPECT_LT(out.find("HELD"), out.find("BROKEN")) << out;
}

TEST(SystemVerilog2009KeywordSimulation,
     AddedWordsNameStorageUnderIncludedLists) {
  auto result = RunIncludedLists(
      "module m;\n"
      "  reg [7:0] accept_on      = 8'd21;\n"
      "  reg [7:0] checker        = 8'd1;\n"
      "  reg [7:0] endchecker     = 8'd1;\n"
      "  reg [7:0] eventually     = 8'd1;\n"
      "  reg [7:0] global         = 8'd1;\n"
      "  reg [7:0] implies        = 8'd1;\n"
      "  reg [7:0] let            = 8'd1;\n"
      "  reg [7:0] nexttime       = 8'd1;\n"
      "  reg [7:0] reject_on      = 8'd1;\n"
      "  reg [7:0] restrict       = 8'd1;\n"
      "  reg [7:0] s_always       = 8'd1;\n"
      "  reg [7:0] s_eventually   = 8'd1;\n"
      "  reg [7:0] s_nexttime     = 8'd1;\n"
      "  reg [7:0] s_until        = 8'd1;\n"
      "  reg [7:0] s_until_with   = 8'd1;\n"
      "  reg [7:0] strong         = 8'd1;\n"
      "  reg [7:0] sync_accept_on = 8'd1;\n"
      "  reg [7:0] sync_reject_on = 8'd1;\n"
      "  reg [7:0] unique0        = 8'd1;\n"
      "  reg [7:0] until          = 8'd1;\n"
      "  reg [7:0] until_with     = 8'd1;\n"
      "  reg [7:0] untyped        = 8'd1;\n"
      "  reg [7:0] weak           = 8'd1;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = accept_on + checker + endchecker + eventually;\n"
      "    result = result + global + implies + let + nexttime;\n"
      "    result = result + reject_on + restrict + s_always + s_eventually;\n"
      "    result = result + s_nexttime + s_until + s_until_with + strong;\n"
      "    result = result + sync_accept_on + sync_reject_on + unique0;\n"
      "    result = result + until + until_with + untyped + weak;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(SystemVerilog2009KeywordSimulation, IncludedVerilog1995RolesStillRun) {
  auto gates = RunSystemVerilog2009(
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

  auto control = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation, IncludedVerilog2001RolesStillRun) {
  auto result = RunSystemVerilog2009(
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

  auto signedness = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation,
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

  const char* const kDeclOnly =
      "module m;\n"
      "  reg [7:0] cell     = 8'd7;\n"
      "  reg [7:0] library  = 8'd9;\n"
      "  reg [7:0] instance = 8'd11;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd0;\n"
      "endmodule\n";
  EXPECT_EQ(RunNoconfigList(kDeclOnly, "cell"), 7u);
  EXPECT_EQ(RunNoconfigList(kDeclOnly, "library"), 9u);
  EXPECT_EQ(RunNoconfigList(kDeclOnly, "instance"), 11u);
}

TEST(SystemVerilog2009KeywordSimulation, IncludedVerilog2005RoleStillRuns) {
  auto result = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation,
     IncludedSystemVerilog2005RolesStillRun) {
  auto types = RunSystemVerilog2009(
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

  auto user_types = RunSystemVerilog2009(
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

  auto statements = RunSystemVerilog2009(
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

  auto processes = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation, ConstantFormsCarryValuesAtRuntime) {
  auto from_literal = RunSystemVerilog2009(
      "module m;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunSystemVerilog2009(
      "module m;\n"
      "  parameter P = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunSystemVerilog2009(
      "module m;\n"
      "  localparam L = 21;\n"
      "  logic [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);

  auto from_function = RunSystemVerilog2009(
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

TEST(SystemVerilog2009KeywordSimulation,
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

  EXPECT_EQ(RunSystemVerilog2009(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_function"), 11u);
}

TEST(SystemVerilog2009KeywordSimulation, LaterWordsRunAsIdentifiers) {
  auto result = RunSystemVerilog2009(
      "module m;\n"
      "  logic [7:0] implements;\n"
      "  logic [7:0] interconnect;\n"
      "  logic [7:0] nettype;\n"
      "  logic [7:0] soft;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    implements   = 8'd21;\n"
      "    interconnect = 8'd1;\n"
      "    nettype      = 8'd0;\n"
      "    soft         = 8'd0;\n"
      "    result = implements * 2 + interconnect + nettype + soft;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
