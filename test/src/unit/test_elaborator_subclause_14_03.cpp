#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingBlockElab, UnnamedNonDefaultBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, UnnamedDefaultBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToInputClockvarError) {
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
             "endmodule\n"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarError) {
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
             "endmodule\n"));
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
             "    cb.bidir = 8'hFF;\n"
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
  // §14.3: a skew that folds to a negative integer violates the non-negative
  // requirement. Literal constant form (§11.2.1).
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #(0-1) a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NegativeParameterOutputSkewRejected) {
  // §14.3 non-negative skew, parameter constant form (§11.2.1).
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  parameter int P = -1;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #P a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NegativeLocalparamSkewRejected) {
  // §14.3 non-negative skew, localparam constant form (§11.2.1).
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  localparam LP = -2;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #LP a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NegativeDefaultInputSkewRejected) {
  // §14.3 non-negative skew applied to the default_skew clocking item.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #(0-1) output #0;\n"
             "    input a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NonNegativeConstantSkewsAccepted) {
  // §14.3 accepting path: zero and positive integer skews, plus a parameter
  // that folds to a non-negative value, are all legal.
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
  // §14.3: a skew delay that is neither a time literal nor a constant
  // expression is illegal. A reference to a plain variable does not fold to a
  // constant and must be rejected.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  logic [7:0] v;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #v a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, TimeLiteralSkewAccepted) {
  // §14.3: a skew delay may be a time literal; it need not fold to a plain
  // integer and shall not be rejected by the non-negative-integer path.
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
  // §14.3 non-negative skew applied to the output half of a default_skew item.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #0 output #(0-1);\n"
             "    output a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, NonNegativeLocalparamSkewAccepted) {
  // §14.3 accepting path for the localparam constant form (§11.2.1).
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
  // §14.3: reading a clockvar whose direction is input is the ordinary sampling
  // operation and shall be legal.
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
  // §14.3: driving a clockvar whose direction is output — via the canonical
  // nonblocking synchronous drive — shall be legal.
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
  // §14.3: the write-to-input prohibition holds for a nonblocking assignment,
  // not only a blocking one.
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
             "endmodule\n"));
}

TEST(ClockingBlockElab, NonIntegerRealSkewRejected) {
  // §14.3: a constant-expression skew that is not a time literal shall evaluate
  // to an integer; a fractional real constant violates that requirement.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #1.5 a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, FractionalTimeLiteralSkewAccepted) {
  // §14.3: a time literal is an acceptable skew even when fractional; the
  // integer requirement applies only to non-time-literal constant expressions.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic a;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #10.5ns a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
