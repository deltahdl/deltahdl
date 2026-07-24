#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1800-2009" region and drives the
// whole pipeline over it -- preprocess, parse, elaborate, lower, simulate --
// returning the final value of `var_name`. The diagnostic check is what keeps
// the result meaningful: source this version's list admits has to run clean,
// not merely produce a number after the front end recovered from something it
// rejected.
uint64_t RunSystemVerilog2009(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2009\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The same wrapper for "1800-2005", the union of the four lists this version
// includes. It is what the added words are measured against: source that runs
// there and cannot be written under this version's list is source the addition
// took away, and source that runs only under this version's list is what the
// addition bought.
uint64_t RunIncludedLists(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2005\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The same wrapper again for the configuration-free companion of "1364-2001".
// Two lists were published for that standard and this version includes one of
// them; the companion is the one that leaves ten words out, so it is the only
// list against which that half of the inclusion can be measured.
uint64_t RunNoconfigList(const std::string& body, const char* var_name) {
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

// Runs the same pipeline but returns what the run wrote to standard output.
// Some of what this version adds reports rather than computes -- an assertion
// inside a checker has no value to read back off a variable -- so the text the
// run produces is the only place its behaviour shows.
std::string RunSystemVerilog2009Output(const std::string& body) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2009\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
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

// The added declaration that produces a value, run rather than merely built. A
// `let` names an expression, and the expression has to be substituted wherever
// the name is used for the number to come out -- which is what separates this
// from the name simply resolving. Both scopes the declaration may be written in
// are here, the compilation unit's own and the design element's, because they
// reach the running design by different paths; and the formal declared with
// `untyped`, the other added word this construct admits, has to take an actual
// of whatever type is handed to it.
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
  // The two-argument let contributes 22, the compilation-unit let 20, and the
  // literal one more: 43.
  EXPECT_EQ(result, 43u);

  // A let taking no arguments at all, spent twice over, so the substitution has
  // to happen at each use rather than once.
  auto reused = RunSystemVerilog2009(
      "module m;\n"
      "  logic [7:0] result;\n"
      "  let step = 21;\n"
      "  initial result = step + step + 8'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(reused, 43u);
}

// The added case qualifier, driving a real branch selection. It qualifies the
// plain case, the wildcard case, and the conditional statement alike -- three
// productions, each reached by its own path -- and each is given a selector
// that matches exactly one branch, so a qualifier that had swallowed the
// statement or picked the wrong arm would show up as a wrong number.
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
  // Twenty from the matching case arm, twelve from the wildcard arm, eleven
  // from the taken conditional branch.
  EXPECT_EQ(result, 43u);

  // The other half of what the qualifier means: no arm need match. The same
  // statement with a selector matching nothing runs through and leaves the
  // running value alone rather than failing or taking a branch.
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

// The added word pair that brackets a design element, run rather than merely
// instantiated. A checker has no value to read back, so what it does shows in
// what its body reports: the assertion inside it is evaluated against the
// signals the instantiation passed in, and its pass and fail action blocks say
// which way it went. The body is written with `assert property`, `property`,
// and `endproperty` from the fourth included list, so the addition is only
// usable because of the inclusion.
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

  // The first clock edge samples a held request and the second samples a
  // dropped one, so the checker's body has to have run twice and reached a
  // different verdict each time.
  EXPECT_NE(out.find("HELD"), std::string::npos) << out;
  EXPECT_NE(out.find("BROKEN"), std::string::npos) << out;
  EXPECT_NE(out.find("END"), std::string::npos) << out;
  EXPECT_LT(out.find("HELD"), out.find("BROKEN")) << out;
}

// The other side of the addition, carried to a run. Every test above shows an
// added word doing its keyword job under this version; this one shows all
// twenty-three of them naming storage that really holds a value under
// "1800-2005", the union of everything this version includes. Without this leg
// the runtime evidence would be consistent with the words having been reserved
// all along rather than added by this version_specifier.
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
  // Twenty-one from the first and one from each of the other twenty-two.
  EXPECT_EQ(result, 43u);
}

// The first included list driven end to end from its own syntax. Inclusion is
// not only about what a word may no longer name: the gate primitives have to go
// on building structure, the resolved net type has to go on combining two
// drivers, and the procedural statements have to go on driving control flow --
// all under a region opened for this version_specifier.
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
  // and(1,1) is 1, nor(1,1) is 0, and a wand resolving two ones is 1.
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
  // Twenty from the for loop, ten from the repeat, two from the while, and one
  // from the matching casez branch.
  EXPECT_EQ(control, 33u);
}

// The second included list at runtime. `automatic` is the entry whose whole
// point is a runtime one -- each call needs storage of its own, which only a
// recursive call shows -- and the value it works against is a `localparam`.
// Both the factorial and the task's accumulation have to survive re-entry for
// this number to come out. These are entries the configuration-free companion
// list keeps as well; the ten it drops are driven end to end by the test below.
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
  // 20 + 3! + 17 = 43.
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
  // The signed copy reads as negative and the unsigned copy does not.
  EXPECT_EQ(signedness, 43u);
}

// The half of the second inclusion that the test above cannot reach, driven end
// to end from the companion list's own directive syntax. Two reserved word
// lists were published for that Verilog standard and they differ on exactly ten
// words; this version includes the one that keeps them, so the ten are reserved
// here and cannot name anything. Under the companion specifier the very same
// ten name storage that really holds a value -- declared, initialized, summed,
// and read back off a completed run. Without this the choice between the two
// lists would rest on front-end evidence alone.
//
// A configuration declaration itself has no runtime form: it says which source
// to bind and leaves nothing behind in a running design. That is why the words
// are exercised here as the identifiers the companion list leaves them, which
// is what makes the difference between the two lists observable at this stage.
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
  // Thirty-four from the first and one from each of the other nine.
  EXPECT_EQ(result, 43u);

  // Each is read back on its own as well, so a name that failed to become
  // storage shows up here rather than being absorbed into a total.
  const char* kDeclOnly =
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

// The third included list at runtime -- one word, and a net type is only fully
// observed once a value travels through it. The scalar net gates the addition
// and the vector net carries it, so the result cannot come out right unless
// both were really built and really driven under this version's list.
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
  // The bus holds 22, doubled and less one is 43, and the flag lets it through.
  EXPECT_EQ(result, 43u);
}

// The fourth included list at runtime, which is the largest thing this version
// inherits and the vocabulary the additions are written alongside. The typed
// storage has to carry values through the widths its words name, the user-
// defined types have to reach the run with the width and members their
// definitions gave them, and the added statements have to drive control flow.
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
  // 20 + 10 + 6 + 4 + 2 + 1 + 0 = 43.
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
  // The third enumeration member stands for 2.
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
  // Two do-while passes give 20; the for loop adds one on i=0 and one on i=2
  // for 22; foreach adds the four array elements for 26; the case arm makes 29;
  // and the membership test adds twice(6) for 41.
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
  // The second edge latches 22 and the combinational block then holds 22 -- the
  // first edge's 21 is overwritten, so a block that never re-ran cannot get
  // here.
  EXPECT_EQ(processes, 44u);
}

// The constant forms this list admits, each reaching the run as an operand. A
// literal and a `parameter` come from the first included list, a `localparam`
// and the `automatic` that lets a constant function be written come from the
// second, and `int` -- the type the function returns and takes -- comes from
// the fourth.
//
// The fifth constant form -- a genvar -- has no test at this stage, and cannot
// have one. It shows its value in the copies its loop produces rather than in a
// width or an operand, so observing it at runtime means giving each pass of the
// loop something to drive and reading the results back after a run. Nothing a
// loop generate construct produces reaches a running design here: the same
// array driven by plain continuous assignments reads back correctly while the
// generated form reads zero, and that holds with no `begin_keywords region at
// all. The fault is in how the construct is lowered, not in which words are
// reserved, so no test here can drive it. The genvar is observed instead at the
// elaborator, where the copies really are produced.
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

// The same constant forms sizing a declaration rather than standing in an
// expression -- the position where a constant expression is actually required,
// and a different path into the running design. Each variable is four bits wide
// and is handed a value too large for it, so the truncation is what proves the
// width really came from the constant.
TEST(SystemVerilog2009KeywordSimulation,
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
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2009(kSrc, "from_function"), 11u);
}

// The negative the five tables imply, carried all the way to a run: a word none
// of them lists is an ordinary identifier under this version, so it can name
// storage that really holds a value, however firmly the next standard reserves
// it. None of the words used here opens a design element, which keeps the
// region machinery -- it tracks design elements by a line's first word, without
// regard to the list in force -- out of the way of the statements below.
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
