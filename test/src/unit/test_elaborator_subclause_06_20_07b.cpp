#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDollarContext =
    "'$' may stand only in a queue's dimension or select, a value range's "
    "bound";

void ExpectDollarReportedOnlyOn(const ElabFixture& f,
                                std::initializer_list<uint32_t> reported,
                                std::initializer_list<uint32_t> accepted) {
  for (uint32_t line : reported) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kDollarContext, line, "6.20.7"))
        << line;
  }
  for (uint32_t line : accepted) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kDollarContext, line, "6.20.7"))
        << line;
  }
}

TEST(DollarConstantElaboration, DollarAsAnOrdinaryOperandIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, y, q[$];\n"
      "  wire [7:0] w;\n"
      "  wire [7:0] v = $;\n"
      "  int z = $;\n"
      "  assign w = $;\n"
      "  function automatic int f();\n"
      "    return $;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = $;\n"
      "    y = $ + 1;\n"
      "    if (x == $) y = 0;\n"
      "    x = q[$];\n"
      "    y = q[$-1];\n"
      "    x = int'(y inside {[0:$]});\n"
      "    y = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 5, 6, 8, 11, 12, 13}, {14, 15, 16, 17});
}

TEST(DollarConstantElaboration,
     DollarAsACallArgumentAPortConnectionOrADefparamValueIsRejected) {
  ElabFixture f;
  Elaborate(
      "module s #(parameter int N = 1)(input int a);\n"
      "endmodule\n"
      "checker c(a);\n"
      "endchecker\n"
      "module top;\n"
      "  int x;\n"
      "  bit clk;\n"
      "  function automatic int f(int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  task automatic t(int a);\n"
      "  endtask\n"
      "  sequence sq(v, n);\n"
      "    v ##[1:n] v;\n"
      "  endsequence\n"
      "  checker nc(a);\n"
      "  endchecker\n"
      "  s u1(.a($));\n"
      "  s u2($);\n"
      "  defparam u1.N = $;\n"
      "  initial begin\n"
      "    x = f($);\n"
      "    t($);\n"
      "    x = f(1);\n"
      "    t(x);\n"
      "  end\n"
      "  c k1($);\n"
      "  nc k2($);\n"
      "  assert property (@(posedge clk) sq(x, $));\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {18, 19, 20, 22, 23}, {24, 25, 27, 28, 29});
}

TEST(DollarConstantElaboration,
     DollarInAPackedOrAnUnboundedUnpackedDimensionIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top(input logic [$:0] p);\n"
      "  logic [$:0] a;\n"
      "  wire [7:$] b;\n"
      "  int c [1:$];\n"
      "  int d [$:3];\n"
      "  int e [$];\n"
      "  typedef logic [$:1] t;\n"
      "  function automatic logic [$:0] f(logic [$:2] v);\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    logic [$:1] g;\n"
      "    int h [$];\n"
      "    int i [1 + $];\n"
      "    int j [$:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {1, 2, 3, 4, 7, 8, 12, 14}, {5, 6, 13, 15});
}

TEST(DollarConstantElaboration, DollarBoundsAValueRangeOnlyStandingAlone) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = int'(y inside {[0:$-1]});\n"
      "    x = int'(y inside {[$+1:5]});\n"
      "    x = int'(y inside {[0:$]});\n"
      "    x = int'(y inside {[$:5], [7:$]});\n"
      "    x = int'(y inside {[5 +/- $]});\n"
      "    case (x) inside\n"
      "      [0:$-1]: y = 0;\n"
      "      [$:-5]: y = 1;\n"
      "      [9:$]: y = 2;\n"
      "    endcase\n"
      "    case (x)\n"
      "      $: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "  assign y = int'(x inside {[1:$ * 2]});\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 5, 8, 10, 15, 18}, {6, 7, 11, 12});
}

TEST(DollarConstantElaboration,
     DollarEndsACycleDelayOrRepetitionRangeOnlyAsItsWholeUpperBound) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  bit clk, a, b;\n"
      "  sequence s1;\n"
      "    a ##[$:3] b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    a ##[1:$-1] b;\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    a ##[1:$] b ##[0:$] a ##[*] b ##[+] a;\n"
      "  endsequence\n"
      "  property p1;\n"
      "    @(posedge clk) a[*$] |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) a[*$:3] |-> b;\n"
      "  endproperty\n"
      "  property p3;\n"
      "    @(posedge clk) a[=1:$-1] |-> b;\n"
      "  endproperty\n"
      "  property p4;\n"
      "    @(posedge clk) a[->$] |-> b;\n"
      "  endproperty\n"
      "  property p5;\n"
      "    @(posedge clk) a[*1:$] ##1 b[=1:$] ##1 a[->1:$] ##1 b[*] |-> a;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) a ##($) b);\n"
      "  a2: assert property (@(posedge clk) a ##[$+1:4] b);\n"
      "  a3: assert property (@(posedge clk) a ##[2:$] b);\n"
      "  always @(posedge clk) begin\n"
      "    a4: assert property (a[*2:$-1] ##1 b);\n"
      "    a5: assert property (a[*2:$] ##1 b);\n"
      "  end\n"
      "  a6: assert property (@(posedge clk) a ##$ b);\n"
      "  a7: assert property (@(posedge clk) a ##[$:$] b);\n"
      "  a8: assert property (@(posedge clk) ##3 a ##[0:$] b);\n"
      "  a9: assert property (@(posedge clk) b[->$:3] ##1 a);\n"
      "  a10: assert property (@(posedge clk) b[=$] ##1 a);\n"
      "  a11: assert property (@(posedge clk) b[->1:3] ##1 a[=0:$]);\n"
      "  sequence s4;\n"
      "    ##$ a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(
      f, {4, 7, 13, 16, 19, 22, 27, 28, 31, 34, 35, 37, 38, 41},
      {10, 25, 29, 32, 36, 39});
}

TEST(DollarConstantElaboration,
     DollarEndsAnAlwaysOrEventuallyRangeOnlyAsItsWholeUpperBound) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  bit clk, a;\n"
      "  property p1;\n"
      "    @(posedge clk) always [$:3] a;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) s_eventually [1:$-1] a;\n"
      "  endproperty\n"
      "  property p3;\n"
      "    @(posedge clk) always [1:$] a;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) s_eventually [$:2] a);\n"
      "  a2: assert property (@(posedge clk) always [2:$+1] a);\n"
      "  a3: assert property (@(posedge clk) s_eventually [2:$] a);\n"
      "  a4: assert property (@(posedge clk) s_always [1:$-1] a);\n"
      "  a5: assert property (@(posedge clk) eventually [$:2] a);\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 7, 12, 13, 15, 16}, {10, 14});
}

TEST(DollarConstantElaboration,
     DollarIsJudgedInsideEveryGenerateBlockWithItsOwnDeclarations) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, q[$];\n"
      "  int a [4];\n"
      "  int s [4];\n"
      "  if (1) begin : g\n"
      "    int b [4];\n"
      "    int s [$];\n"
      "    int z = $;\n"
      "    int k = s[$];\n"
      "    logic [$:0] p;\n"
      "    initial begin\n"
      "      x = b[$];\n"
      "      x = a[$];\n"
      "      x = q[$ - 1];\n"
      "      x = int'(x inside {[1:$]});\n"
      "      x = int'(x inside {[1:$ - 1]});\n"
      "      x = s[$ - 1];\n"
      "    end\n"
      "  end\n"
      "  initial x = s[$];\n"
      "  if ($ > 0) begin : h\n"
      "  end else begin : e\n"
      "    int f = $;\n"
      "    int m = 1;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n"
      "    int c = $ + i;\n"
      "    int d = i;\n"
      "  end\n"
      "  case (1)\n"
      "    $: begin : c1\n"
      "    end\n"
      "    1: begin : c2\n"
      "      int e = $;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {8, 10, 12, 13, 16, 20, 21, 23, 27, 31, 34},
                             {9, 14, 15, 17, 24, 28});
}

TEST(DollarConstantElaboration,
     DollarIsJudgedInAnInterfaceAProgramAndAChecker) {
  ElabFixture f;
  Elaborate(
      "interface ifc;\n"
      "  int x, q[$];\n"
      "  int a [4];\n"
      "  int z = $;\n"
      "  initial begin\n"
      "    x = a[$];\n"
      "    x = q[$];\n"
      "  end\n"
      "endinterface\n"
      "checker chk(logic clk);\n"
      "  function automatic int f(int v[$], int w[2]);\n"
      "    int u = v[$];\n"
      "    return u + w[$];\n"
      "  endfunction\n"
      "  function automatic int g();\n"
      "    return $;\n"
      "  endfunction\n"
      "endchecker\n"
      "program prg;\n"
      "  int x, q[$];\n"
      "  int a [4];\n"
      "  initial begin\n"
      "    x = $;\n"
      "    x = a[$ - 1];\n"
      "    x = q[$ - 1];\n"
      "    x = int'(x inside {[0:$]});\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  ifc i1();\n"
      "  chk c1(clk);\n"
      "  prg p1();\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 6, 13, 16, 23, 24}, {7, 12, 25, 26});
}

TEST(DollarConstantElaboration,
     DollarSelectsOnlyAQueueAmongASubroutinesArgumentsAndLocals) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, q[$];\n"
      "  int s [4];\n"
      "  function automatic int f(int a[4], int b[$], int c = $);\n"
      "    int d [2];\n"
      "    int s [$];\n"
      "    x = a[$];\n"
      "    x = b[$];\n"
      "    x = d[$ - 1];\n"
      "    x = s[$];\n"
      "    return q[$];\n"
      "  endfunction\n"
      "  task automatic t(int k = 1);\n"
      "    int e [3];\n"
      "    x = e[$];\n"
      "    x = k;\n"
      "  endtask\n"
      "  initial begin\n"
      "    int g [2];\n"
      "    x = g[$];\n"
      "    x = s[$];\n"
      "  end\n"
      "  initial begin\n"
      "    int h [$];\n"
      "    x = h[$];\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 7, 9, 15, 20, 21}, {8, 10, 11, 16, 25});
}

TEST(DollarConstantElaboration, DollarIsJudgedInAPackageAndTheCompilationUnit) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  int pa [4];\n"
      "  int pq [$];\n"
      "  int pz = $;\n"
      "  logic [$:0] pv;\n"
      "  typedef logic [1:$] pt;\n"
      "  function automatic int pf(int k);\n"
      "    if (k == $) return 0;\n"
      "    return pa[$];\n"
      "  endfunction\n"
      "  function automatic int pg();\n"
      "    return pq[$] + pq[$ - 1];\n"
      "  endfunction\n"
      "endpackage\n"
      "int ua [4];\n"
      "int uz = $;\n"
      "logic [7:$] uv;\n"
      "typedef logic [$:2] ut;\n"
      "function automatic int uf();\n"
      "  return ua[$];\n"
      "endfunction\n"
      "function automatic int ug(int v[$]);\n"
      "  return v[$ - 1];\n"
      "endfunction\n"
      "module top;\n"
      "  import p::*;\n"
      "  int x = int'(pz inside {[0:$]});\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 5, 6, 8, 9, 16, 17, 18, 20}, {12, 23, 27});
}

TEST(DollarConstantElaboration,
     DollarIsJudgedInAClassItsConstraintsAndAnInlineConstraint) {
  ElabFixture f;
  Elaborate(
      "class Base;\n"
      "  function new(int k = 0);\n"
      "  endfunction\n"
      "endclass\n"
      "class C extends Base;\n"
      "  rand int a [4];\n"
      "  rand int q [$];\n"
      "  rand int x;\n"
      "  int z = $;\n"
      "  logic [$:0] cv;\n"
      "  constraint c1 { x dist {[0:$] := 1}; }\n"
      "  constraint c2 { x dist {[0:$ - 1] := 1}; }\n"
      "  constraint c3 { x dist {$ := 1}; }\n"
      "  constraint c4 { x dist {[0:9] := $}; }\n"
      "  constraint c5 { x inside {[1:$]}; }\n"
      "  constraint c6 { a[$] == 1; }\n"
      "  constraint c7 { q[$] == 1; }\n"
      "  constraint c8 { if (x > $) x < 3; }\n"
      "  constraint c9 { x dist {[$:9] :/ 1, 10 := 2}; }\n"
      "  function new();\n"
      "    super.new($);\n"
      "  endfunction\n"
      "  function int m(int k);\n"
      "    int l [2];\n"
      "    if (k == $) return 0;\n"
      "    return l[$];\n"
      "  endfunction\n"
      "  function int n();\n"
      "    return q[$ - 1];\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends Base($);\n"
      "endclass\n"
      "class E extends Base(1);\n"
      "endclass\n"
      "package p;\n"
      "  class PC;\n"
      "    int pz = $;\n"
      "    int pq [$];\n"
      "    function int f();\n"
      "      return pq[$];\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  class MC;\n"
      "    int ma [3];\n"
      "    function int f();\n"
      "      return ma[$];\n"
      "    endfunction\n"
      "  endclass\n"
      "  C obj = new;\n"
      "  initial begin\n"
      "    void'(obj.randomize() with { x dist {[0:$ - 1] := 1}; });\n"
      "    void'(obj.randomize() with { x dist {[1:$] := 1}; });\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(
      f, {9, 10, 12, 13, 14, 16, 18, 21, 25, 26, 32, 38, 49, 54},
      {11, 15, 17, 19, 29, 34, 41, 55});
}

TEST(
    DollarConstantElaboration,
    DollarStandsInADeclaredSequenceOrPropertyOnlyAsARangesUpperBoundOrAWholeActual) {
  ElabFixture f;
  Elaborate(
      "checker ck(x, n);\n"
      "endchecker\n"
      "module top;\n"
      "  bit clk, a, b;\n"
      "  property p1;\n"
      "    @(posedge clk) a ##[$:3] b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) a ##[$:$] b;\n"
      "  endproperty\n"
      "  property p3;\n"
      "    @(posedge clk) ##$ a;\n"
      "  endproperty\n"
      "  property p4;\n"
      "    @(posedge clk) a ##[1:$] b;\n"
      "  endproperty\n"
      "  sequence s1;\n"
      "    a[*$] ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    a ##1 b[->$:3];\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    a ##1 b[=$];\n"
      "  endsequence\n"
      "  sequence s4;\n"
      "    a[*1:$] ##1 b[->1:3] ##1 a[=0:$];\n"
      "  endsequence\n"
      "  sequence s5(x, n);\n"
      "    x ##[1:n] x;\n"
      "  endsequence\n"
      "  property p5(x, n = $);\n"
      "    @(posedge clk) x ##[1:n] x;\n"
      "  endproperty\n"
      "  property p6(x, n = $ + 1);\n"
      "    @(posedge clk) x ##[1:n] x;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) s5(a, $));\n"
      "  assert property (@(posedge clk) s5(a, $ - 1));\n"
      "  assert property (@(posedge clk) a ##1 (b == $));\n"
      "  assert property (@(posedge clk) disable iff ($) a);\n"
      "  ck k1(a, $);\n"
      "  ck k2(a, $ + 1);\n"
      "  sequence s6;\n"
      "    s5(a, $ - 1) ##1 b;\n"
      "  endsequence\n"
      "  sequence s7;\n"
      "    s5(a, $) ##1 b;\n"
      "  endsequence\n"
      "  assert property (p5(a, $ + 2));\n"
      "  assert property (p5(a, $));\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f,
                             {6, 9, 12, 18, 21, 24, 35, 39, 40, 41, 43, 45, 50},
                             {15, 27, 32, 38, 42, 48, 51});
}

TEST(DollarConstantElaboration,
     DollarIsJudgedInACoverSequenceAnExpectASequenceActualAndADist) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  bit clk, a, b;\n"
      "  sequence s(x);\n"
      "    x ##1 b;\n"
      "  endsequence\n"
      "  cover sequence (@(posedge clk) a ##[$:2] b);\n"
      "  cover sequence (@(posedge clk) a ##[2:$] b);\n"
      "  cover sequence (@(posedge clk) a[*$:2] ##1 b);\n"
      "  assert property (@(posedge clk) s(b[*$:2]));\n"
      "  assert property (@(posedge clk) s(b[*2:$]));\n"
      "  assert property (@(posedge clk) a dist {[0:1] := $});\n"
      "  assert property (@(posedge clk) a dist {[0:$] := 1});\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a ##1 b[->$]);\n"
      "    expect (@(posedge clk) a ##1 b[->1:$]);\n"
      "    expect (@(posedge clk) a ##[1:$ - 1] b);\n"
      "  end\n"
      "  task t;\n"
      "    expect (@(posedge clk) a ##[$:1] b);\n"
      "    expect (@(posedge clk) a ##[1:$] b);\n"
      "  endtask\n"
      "  class c;\n"
      "    bit clk, a, b;\n"
      "    task m;\n"
      "      expect (@(posedge clk) a[=$] ##1 b);\n"
      "      expect (@(posedge clk) a[=1:$] ##1 b);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {6, 8, 9, 11, 14, 16, 19, 25},
                             {7, 10, 12, 15, 20, 26});
}

TEST(
    DollarConstantElaboration,
    DollarIsJudgedInTheAssertionsOfEveryDesignElementGenerateAndClockingBlock) {
  ElabFixture f;
  Elaborate(
      "interface ifc(input bit clk);\n"
      "  bit a, b;\n"
      "  sequence si;\n"
      "    a ##[$:2] b;\n"
      "  endsequence\n"
      "  assert property (@(posedge clk) a[*$] ##1 b);\n"
      "  assert property (@(posedge clk) a[*1:$] ##1 b);\n"
      "endinterface\n"
      "program prg(input bit clk);\n"
      "  bit a, b;\n"
      "  property pp;\n"
      "    @(posedge clk) always [$:3] a;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) a ##[1:$] b);\n"
      "endprogram\n"
      "checker chk(logic clk, logic a);\n"
      "  assert property (@(posedge clk) a ##[1:$ - 1] a);\n"
      "  assert property (@(posedge clk) a ##[1:$] a);\n"
      "  property pk;\n"
      "    @(posedge clk) a[*$:1];\n"
      "  endproperty\n"
      "  sequence sk;\n"
      "    a[*0:$];\n"
      "  endsequence\n"
      "endchecker\n"
      "module top;\n"
      "  bit clk, a, b;\n"
      "  ifc i1(clk);\n"
      "  prg p1(clk);\n"
      "  chk c1(clk, a);\n"
      "  if (1) begin : g\n"
      "    sequence sg;\n"
      "      a ##1 b[=$];\n"
      "    endsequence\n"
      "    assert property (@(posedge clk) a ##[$:1] b);\n"
      "    assert property (@(posedge clk) a[*1:$ - 1] ##1 b);\n"
      "    assert property (@(posedge clk) a ##[0:$] b);\n"
      "    always @(posedge clk) assert property (@(posedge clk) s_eventually "
      "[$:2] a);\n"
      "  end\n"
      "  clocking cb @(posedge clk);\n"
      "    property pc;\n"
      "      a ##[$:2] b;\n"
      "    endproperty\n"
      "    sequence sc;\n"
      "      a ##[2:$] b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {4, 6, 12, 17, 20, 33, 35, 36, 38, 42},
                             {7, 14, 18, 23, 37, 45});
}

TEST(DollarConstantElaboration,
     DollarIsJudgedInTheSequencesAndPropertiesOfAPackageAndTheCompilationUnit) {
  ElabFixture f;
  Elaborate(
      "package p;\n"
      "  sequence ps(x, y);\n"
      "    x ##[$:2] y;\n"
      "  endsequence\n"
      "  sequence pt(x, y);\n"
      "    x ##[1:$] y;\n"
      "  endsequence\n"
      "  property pp(x);\n"
      "    always [1:$ - 1] x;\n"
      "  endproperty\n"
      "endpackage\n"
      "sequence us(x, y);\n"
      "  x[*$:2] ##1 y;\n"
      "endsequence\n"
      "sequence uo(x, y);\n"
      "  x ##[2:$ - 1] y;\n"
      "endsequence\n"
      "property up(x, y);\n"
      "  x |-> ##[0:$] y;\n"
      "endproperty\n"
      "property uq(x, n = $);\n"
      "  x ##[1:n] x;\n"
      "endproperty\n"
      "module top;\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(f, {3, 9, 13, 16}, {6, 19, 21});
}

TEST(DollarConstantElaboration,
     DollarInACovergroupStandsOnlyAsAValueRangesBoundOrAMatchesCount) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  bit [3:0] pv;\n"
      "  covergroup pcg;\n"
      "    coverpoint pv {\n"
      "      bins a = {$};\n"
      "      bins b = {[2:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endpackage\n"
      "bit [3:0] uv;\n"
      "covergroup ucg;\n"
      "  coverpoint uv {\n"
      "    bins a = {$};\n"
      "    bins b = {[$:5]};\n"
      "  }\n"
      "endgroup\n"
      "class C;\n"
      "  bit [3:0] cv;\n"
      "  covergroup ccg;\n"
      "    coverpoint cv {\n"
      "      bins a = {$};\n"
      "      bins b = {[2:$]};\n"
      "    }\n"
      "  endgroup\n"
      "  function new;\n"
      "    ccg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "interface ifc(input bit clk);\n"
      "  bit [3:0] iv;\n"
      "  covergroup icg @(posedge clk);\n"
      "    coverpoint iv {\n"
      "      bins a = {$};\n"
      "      bins b = {[2:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endinterface\n"
      "program prg(input bit clk);\n"
      "  bit [3:0] rv;\n"
      "  covergroup rcg @(posedge clk);\n"
      "    coverpoint rv {\n"
      "      bins a = {$};\n"
      "      bins b = {[2:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endprogram\n"
      "checker chk(bit clk);\n"
      "  bit [3:0] kv;\n"
      "  covergroup kcg @(posedge clk);\n"
      "    coverpoint kv {\n"
      "      bins a = {$};\n"
      "      bins b = {[2:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endchecker\n"
      "module top;\n"
      "  bit clk;\n"
      "  bit [3:0] a, b;\n"
      "  ifc i1(clk);\n"
      "  prg p1(clk);\n"
      "  chk c1(clk);\n"
      "  covergroup cg @(posedge clk);\n"
      "    cpa: coverpoint a {\n"
      "      bins v1 = {$};\n"
      "      bins v2 = {[$:5]};\n"
      "      bins v3 = {[2:$]};\n"
      "      bins v4[$] = {[0:3]};\n"
      "      bins v5[] = {[0:3]} with (item < $);\n"
      "      bins v6[] = {[0:3]} with (item < 2);\n"
      "      bins v7 = {1} iff ($);\n"
      "      bins v8 = (1 => [0:$]);\n"
      "      bins v9 = (1 [* $] => 2);\n"
      "      bins v10 = (1 [*2:$] => 2);\n"
      "      bins v11 = (1 [*2:3] => 2);\n"
      "      option.weight = $;\n"
      "      option.weight = 2;\n"
      "    }\n"
      "    cpb: coverpoint b iff ($);\n"
      "    cpc: coverpoint $;\n"
      "    cpd: coverpoint b iff (clk);\n"
      "    bit [$:0] cpe: coverpoint a;\n"
      "    x: cross cpa, cpb {\n"
      "      bins s1 = binsof(cpa) intersect {[0:$]};\n"
      "      bins s2 = binsof(cpa) intersect {$};\n"
      "      bins s3 = binsof(cpa) with (cpa > $);\n"
      "      bins s4 = binsof(cpa) with (cpa > 1) matches $;\n"
      "      option.weight = $;\n"
      "    }\n"
      "    y: cross cpa, cpd iff ($);\n"
      "  endgroup\n"
      "  covergroup cg2(int lo = $) @(posedge clk);\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  if (1) begin : g\n"
      "    covergroup gcg @(posedge clk);\n"
      "      coverpoint a {\n"
      "        bins a1 = {$};\n"
      "        bins a2 = {[$:5]};\n"
      "      }\n"
      "    endgroup\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarReportedOnlyOn(
      f, {5,  13, 21, 33, 42, 51, 64, 67, 68, 70, 72,
          73, 75, 78, 79, 81, 84, 85, 87, 89, 91, 97},
      {6, 14, 22, 34, 43, 52, 65, 66, 69, 71, 74, 76, 80, 83, 86, 98});
}

}  // namespace
