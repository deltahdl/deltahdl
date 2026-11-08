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

}  // namespace
