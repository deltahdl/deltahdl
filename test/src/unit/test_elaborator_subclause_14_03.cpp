#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingBlockElab, UnnamedNonDefaultBlockError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-default clocking block must have a name", 2,
                            "14.3"));
}

TEST(ClockingBlockElab, UnnamedDefaultBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToInputClockvarError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data = 1;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 8, "14.3"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.data;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "read from output clockvar 'cb.data'", 8, "14.3"));
}

TEST(ClockingBlockElab, InoutClockvarReadOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.bidir;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, InoutClockvarWriteOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.bidir <= 8'hFF;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NamedClockingBlockWithMultipleSignalsElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a, b, c;\n"
             "  clocking cb @(posedge clk);\n"
             "    input a;\n"
             "    output b;\n"
             "    inout c;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, DefaultInputAndOutputSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #1step output #0;\n"
             "    input a;\n"
             "    output b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, ClockingBlockNegedgeEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data;\n"
             "  clocking cb @(negedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NegativeConstantInputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #(0-1) a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "input skew of clocking signal 'a' is negative (-1); a "
                    "clocking skew has to be a whole number of zero or more",
                    5, "14.3"));
}

TEST(ClockingBlockElab, NegativeParameterOutputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  parameter int P = -1;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #P a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "output skew of clocking signal 'a' is negative (-1); a "
                    "clocking skew has to be a whole number of zero or more",
                    6, "14.3"));
}

TEST(ClockingBlockElab, NegativeLocalparamSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  localparam LP = -2;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #LP a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "input skew of clocking signal 'a' is negative (-2); a "
                    "clocking skew has to be a whole number of zero or more",
                    6, "14.3"));
}

TEST(ClockingBlockElab, NegativeDefaultInputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #(0-1) output #0;\n"
             "    input a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default input skew is negative (-1); a clocking "
                            "skew has to be a whole number of zero or more",
                            5, "14.3"));
}

TEST(ClockingBlockElab, NonNegativeConstantSkewsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 3;\n"
             "  logic clk;\n"
             "  logic a, b, c;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #P a;\n"
             "    output #0 b;\n"
             "    inout c;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NonConstantSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  logic [7:0] v;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #v a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this clocking skew is not a constant expression; "
                            "only constants and parameters may set a skew",
                            6, "14.4"));
}

TEST(ClockingBlockElab, TimeLiteralSkewAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #10ns a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NegativeDefaultOutputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #0 output #(0-1);\n"
             "    output a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default output skew is negative (-1); a clocking "
                            "skew has to be a whole number of zero or more",
                            5, "14.3"));
}

TEST(ClockingBlockElab, NonNegativeLocalparamSkewAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam LP = 2;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #LP a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, ReadFromInputClockvarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToOutputClockvarNonblockingOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data <= 8'hAA;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToInputClockvarNonblockingError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data <= 8'hAA;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 8, "14.3"));
}

TEST(ClockingBlockElab, NonIntegerRealSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #1.5 a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "input skew of clocking signal 'a' is not an integer (1.5); a clocking "
      "skew has to be a whole number of zero or more",
      5, "14.3"));
}

TEST(ClockingBlockElab, FractionalTimeLiteralSkewAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #10.5ns a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, SignalSkewNamesTheSignal) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #0;\n"
             "    input #(0-1) a;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking signal 'a' is negative (-1)", 6, "14.3"));
}

TEST(ClockingBlockElab, NonNegativeIntegerSkewStillAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 a;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, WriteToInputClockvarInForkArmError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    fork\n"
             "      cb.data = r;\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 9, "14.3"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarInAssertionActionBlockError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    assert (1) r = cb.data;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "read from output clockvar 'cb.data'", 8, "14.3"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarOutsideAnAssignmentError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    if (cb.data) r = 1;\n"
             "    @(cb.data);\n"
             "    r = cb.data[0];\n"
             "    case (cb.data) default: ; endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  for (uint32_t line : {8u, 9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "read from output clockvar 'cb.data'", line,
                              "14.3"));
  }
}

TEST(ClockingBlockElab, WriteToSelectOfInputClockvarError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [3:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data[0] <= 1'b1;\n"
             "    cb.data[3:2] <= 2'b01;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 8, "14.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 9, "14.3"));
}

TEST(ClockingBlockElab, ClockvarDirectionInSubroutineAndGenerateError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] i, o, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    input i;\n"
             "    output o;\n"
             "  endclocking\n"
             "  task t; cb.i <= 1; endtask\n"
             "  function void fn; r = cb.o; endfunction\n"
             "  if (1) begin : g\n"
             "    initial cb.i <= 2;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.i'", 8, "14.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "read from output clockvar 'cb.o'", 9, "14.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.i'", 11, "14.3"));
}

TEST(ClockingBlockElab, ClockingSignalNamingNothingError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, d;\n"
             "  clocking cb @(posedge clk);\n"
             "    input d, nosuch;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking signal 'nosuch' names no net or variable",
                            3, "14.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "clocking signal 'd' names no net or variable", 3,
                             "14.3"));
}

TEST(ClockingBlockElab, ClockingSignalsOfTheEnclosingScopeOk) {
  EXPECT_TRUE(
      ElabOk("module m(input logic clk, input logic p);\n"
             "  clocking cb @(posedge clk);\n"
             "    input p, late;\n"
             "  endclocking\n"
             "  logic late, outer;\n"
             "  module inner;\n"
             "    clocking ic @(posedge clk);\n"
             "      input outer;\n"
             "    endclocking\n"
             "  endmodule\n"
             "  inner u();\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, ClockingSignalOnAProceduralOnlyVariableError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  class C; int f; endclass\n"
             "  logic clk;\n"
             "  int d[];\n"
             "  int q[$];\n"
             "  int fa[4];\n"
             "  C h;\n"
             "  task automatic t; int v; endtask\n"
             "  clocking cb @(posedge clk);\n"
             "    input a = d[0];\n"
             "    input b = q[1];\n"
             "    input c = fa[2];\n"
             "    input e = h.f;\n"
             "    input g = t.v;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  for (std::string_view sig : {"'a'", "'b'", "'e'", "'g'"}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("clocking signal {} designates a variable", sig), 9,
        "14.3"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "clocking signal 'c' designates a variable", 9,
                             "14.3"));
}

TEST(ClockingBlockElab, ADeclarationInAnUnnamedBlockIsNotReferenced) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  default clocking @(posedge clk);\n"
      "    input a;\n"
      "    property pu; a; endproperty\n"
      "    sequence su; a; endsequence\n"
      "  endclocking\n"
      "  assert property (pu);\n"
      "  cover property (su);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'pu'", 8,
                            "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'su'", 9,
                            "23.9"));
}

TEST(ClockingBlockElab, ADeclarationInANamedBlockIsReachedThroughItsName) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic clk, a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input a;\n"
             "    property pn; a; endproperty\n"
             "    sequence sn; a; endsequence\n"
             "  endclocking\n"
             "  assert property (cb.pn);\n"
             "  cover property (cb.sn);\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, DISABLED_AClockingSignalNamingNoNetOrVariableError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module s; endmodule\n"
             "module m;\n"
             "  parameter P = 1;\n"
             "  localparam L = 2;\n"
             "  typedef int T;\n"
             "  function int fn(); return 1; endfunction\n"
             "  s inst();\n"
             "  genvar g;\n"
             "  logic clk, v;\n"
             "  wire w;\n"
             "  event ev;\n"
             "  clocking cb @(posedge clk);\n"
             "    input P, L, T, fn, inst, g;\n"
             "    input v, w, ev;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  for (std::string_view sig : {"P", "L", "T", "fn", "inst", "g"}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("clocking signal '{}' names no net or variable", sig), 12,
        "14.3"))
        << sig;
  }
  for (std::string_view sig : {"v", "w", "ev"}) {
    EXPECT_FALSE(ReportedError(
        f.diag.Diagnostics(),
        std::format("clocking signal '{}' names no net or variable", sig), 12,
        "14.3"))
        << sig;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

}  // namespace
