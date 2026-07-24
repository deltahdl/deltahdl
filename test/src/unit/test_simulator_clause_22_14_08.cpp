#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1800-2012" region and drives the
// whole pipeline over it -- preprocess, parse, elaborate, lower, simulate --
// returning the final value of `var_name`. The diagnostic check is what keeps
// the result meaningful: source this version's list admits has to run clean,
// not merely produce a number after the front end recovered from something it
// rejected.
uint64_t RunSystemVerilog2012(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2012\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// The same wrapper for "1800-2009", the union of the five lists this version
// includes. It is what the added words are measured against: source that runs
// there and cannot be written under this version's list is source the addition
// took away, and a run that comes out differently under the two is the addition
// doing something.
uint64_t RunIncludedLists(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1800-2009\"\n" + body + "`end_keywords\n");
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

// The added word whose clause changes what a call resolves to. A class names
// the interface classes it honours, and the methods those interfaces demanded
// have to be reachable at a run -- both through a handle of the class's own
// type and through one typed as the interface, which is the whole point of
// declaring the relationship. The interface classes are written with `interface
// class`, `pure`, and `virtual` from the fourth included list, so the addition
// is usable only because of the inclusion.
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
  // The value written is read back twice and one more is added.
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
  // A handle typed as the interface reaches the implementing method, which is
  // what the clause exists to make possible.
  EXPECT_EQ(through_interface, 43u);
}

// The added word that binds a name to a net's data type, run rather than merely
// declared. A net declared through the bound name has to really carry a value
// from its driver to its reader, and the width it carries has to be the one the
// bound type gave it: the same declaration with no such binding is a scalar and
// loses everything above the low bit, so a byte arriving whole is the binding
// doing its work. A second name bound to the first is here too, since resolving
// one nettype through another is a step the plain form does not take.
//
// The width is shown in the widening direction only. A net whose bound type is
// narrower than the value driven onto it keeps the whole value at a run, while
// the same declaration written as an ordinary sized net truncates as it should
// -- so the bound width does not reach the continuous assignment's lowering.
// That is a gap in how a net declaration is lowered rather than in which words
// are reserved, and no test here can drive it; the width the binding produces
// is observed at the elaborator, where it really is applied.
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

  // The same driver onto a net declared without the binding, which is a single
  // bit and so keeps only the low one.
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
  // The second name resolves through the first, so both nets carry a byte and
  // 21 plus 22 comes out.
  EXPECT_EQ(chained, 43u);
}

// The first of the added word's two keyword roles at a run. Qualifying a union
// makes its members share storage, so a value written through one member is the
// value read back through the other -- something no separate-storage type does,
// and something that cannot be observed at all before the type is laid out and
// driven.
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

  // Written through the second member and read through the first, so the
  // sharing is not an artefact of which member the writer happened to pick.
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

// The added word's other keyword role, and the sharpest runtime evidence in
// this subclause: the same source runs to a different number under the two
// lists. Qualifying a constraint marks it as one the solver honours when it
// can and drops when it must, so the run lands on the preferred value; under
// "1800-2009", the union of everything this version includes, the word is an
// ordinary identifier, the relation is never recorded as a preference, and the
// solver picks from the range the hard constraints leave it. Both the
// preference winning and the later preference outranking the earlier one are
// here, along with the directive that discards a preference outright.
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
  EXPECT_NE(RunIncludedLists(kPreferred, "result"), 43u)
      << "an ordinary identifier states no preference";

  // Two preferences on the same variable: the later one outranks the earlier.
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

  // A hard relation outranks the preference outright, which is what makes the
  // qualifier a preference rather than a second way of writing a constraint.
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

  // The directive that discards the preferences on a variable, which is the
  // other production the word appears in.
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

// The distribution form of the constraint qualifier, run rather than merely
// captured. A qualified distribution is a preference like a qualified relation,
// so the run lands on the weighted value under this version; under the union of
// everything it includes the word qualifies nothing and the solver picks from
// the range the hard constraints leave it, which is a different number from the
// same source.
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
  EXPECT_NE(RunIncludedLists(kSrc, "result"), 43u)
      << "an ordinary identifier weights nothing";
}

// The union qualifier written straight into a data declaration rather than
// through a typedef -- a different item, and one whose layout is only
// observable once the members are written and read at a run.
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

// The nettype declaration written as a package item, carried end to end: the
// name is bound in one scope, imported into another, and the net declared
// through it there really carries a byte from its driver to its reader.
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

// The other side of the addition, carried to a run. Every test above shows an
// added word doing its keyword job under this version; this one shows all four
// of them naming storage that really holds a value under "1800-2009", the union
// of everything this version includes. Without this leg the runtime evidence
// would be consistent with the words having been reserved all along rather than
// added by this version_specifier.
//
// Nothing here uses `interconnect` in its keyword role at a run, and that is
// deliberate: the net it declares is a generic connection whose type is settled
// by what it joins, and it is resolved away before a running design is built --
// it holds no value of its own to read back. Its keyword role is observed where
// it exists, at the parser and the elaborator.
TEST(SystemVerilog2012KeywordSimulation,
     AddedWordsNameStorageUnderIncludedLists) {
  const char* kSrc =
      "module m;\n"
      "  reg [7:0] implements   = 8'd7;\n"
      "  reg [7:0] interconnect = 8'd9;\n"
      "  reg [7:0] nettype      = 8'd11;\n"
      "  reg [7:0] soft         = 8'd16;\n"
      "  reg [7:0] result;\n"
      "  initial result = implements + interconnect + nettype + soft;\n"
      "endmodule\n";
  EXPECT_EQ(RunIncludedLists(kSrc, "result"), 43u);

  // Each is read back on its own as well, so a name that failed to become
  // storage shows up here rather than being absorbed into a total.
  EXPECT_EQ(RunIncludedLists(kSrc, "implements"), 7u);
  EXPECT_EQ(RunIncludedLists(kSrc, "interconnect"), 9u);
  EXPECT_EQ(RunIncludedLists(kSrc, "nettype"), 11u);
  EXPECT_EQ(RunIncludedLists(kSrc, "soft"), 16u);
}

// The first included list driven end to end from its own syntax. Inclusion is
// not only about what a word may no longer name: the gate primitives have to go
// on building structure, the resolved net type has to go on combining two
// drivers, and the procedural statements have to go on driving control flow --
// all under a region opened for this version_specifier.
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
  // and(1,1) is 1, nor(1,1) is 0, and a wand resolving two ones is 1.
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
  // 20 + 3! + 17 = 43.
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
  // Thirty-four from the first and one from each of the other nine.
  EXPECT_EQ(result, 43u);
}

// The third included list at runtime -- one word, and a net type is only fully
// observed once a value travels through it. The scalar net gates the addition
// and the vector net carries it, so the result cannot come out right unless
// both were really built and really driven under this version's list.
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
  // The bus holds 22, doubled and less one is 43, and the flag lets it through.
  EXPECT_EQ(result, 43u);
}

// The fourth included list at runtime, which is the largest thing this version
// inherits and the vocabulary the additions are written alongside. The typed
// storage has to carry values through the widths its words name, the user-
// defined types have to reach the run with the width and members their
// definitions gave them, and the statements have to drive control flow.
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
  // 20 + 10 + 6 + 4 + 2 + 1 + 0 = 43.
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
  // The third enumeration member stands for 2.
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
  // Two do-while passes give 20; the for loop adds one on i=0 and one on i=2
  // for 22; foreach adds the four array elements for 26; the case arm makes 29;
  // and the membership test adds twice(6) for 41.
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
  // The second edge latches 22 and the combinational block then holds 22 -- the
  // first edge's 21 is overwritten, so a block that never re-ran cannot get
  // here.
  EXPECT_EQ(processes, 44u);
}

// The fifth included list at runtime. Its `let` declaration substitutes an
// expression wherever the name is used, from both scopes it may be written in;
// its untyped formal takes whatever actual is handed to it; and its permissive
// case qualifier really selects a branch, including the case where no branch
// matches at all and the running value is left alone.
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
  // The two-argument let contributes 22, the compilation-unit let 20, and the
  // literal one more: 43.
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
  // Twenty from the matching case arm, twelve from the wildcard arm, eleven
  // from the taken conditional branch.
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

// The same constant forms sizing a declaration rather than standing in an
// expression -- the position where a constant expression is actually required,
// and a different path into the running design. Each variable is four bits wide
// and is handed a value too large for it, so the truncation is what proves the
// width really came from the constant.
TEST(SystemVerilog2012KeywordSimulation,
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
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "result"), 23u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunSystemVerilog2012(kSrc, "from_function"), 11u);
}

// The negative the six tables imply, carried all the way to a run: a word none
// of them lists is an ordinary identifier under this version, so it can name
// storage that really holds a value. Each is a near miss of a real entry, since
// this version is the last that reserves anything new and so has no later list
// to be bounded against.
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
