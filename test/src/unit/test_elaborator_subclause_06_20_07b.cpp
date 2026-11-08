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

}  // namespace
