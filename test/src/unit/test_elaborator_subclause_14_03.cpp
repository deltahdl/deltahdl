#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingBlockElab, UnnamedNonDefaultBlockError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  clocking @(posedge clk);\n"
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
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
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
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." A skew that
  // folds to a negative integer breaks the non-negative half. Literal constant
  // form (§11.2.1).
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
  // The skew stands on the input of clocking signal 'a', and `0-1` folds on the
  // integer path of CheckClockingSkew in
  // src/elaborator/elaborator_validate_clocking.cpp, so the report names that
  // signal, the negative half of the requirement, and -1.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "input skew of clocking signal 'a' is negative "
                            "(-1); a clocking skew shall be a non-negative "
                            "integer value",
                            5, "14.3"));
}

TEST(ClockingBlockElab, NegativeParameterOutputSkewRejected) {
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." Parameter
  // constant form (§11.2.1) of a value that breaks the non-negative half.
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
  // `P` folds to -1 on the integer path of CheckClockingSkew in
  // src/elaborator/elaborator_validate_clocking.cpp, so the report names the
  // clocking signal, the negative half of the requirement, and the value.
  //
  // The skew is written on the output of clocking signal 'a', and naming the
  // output half is what this case claims that
  // ClockingBlockElab.NegativeConstantInputSkewRejected does not.
  // MakeClockingSignal in src/parser/parser_clocking.cpp:26 stores an
  // output-only signal's skew in ClockingSignalDecl::skew_delay and leaves
  // out_skew_delay null, so the role a report names reads sig.direction rather
  // than the field the skew arrived in.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output skew of clocking signal 'a' is negative "
                            "(-1); a clocking skew shall be a non-negative "
                            "integer value",
                            6, "14.3"));
}

TEST(ClockingBlockElab, NegativeLocalparamSkewRejected) {
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." Localparam
  // constant form (§11.2.1) of a value that breaks the non-negative half.
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
  // `LP` folds to -2 on the integer path of CheckClockingSkew in
  // src/elaborator/elaborator_validate_clocking.cpp, and the skew stands on the
  // input of clocking signal 'a'.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "input skew of clocking signal 'a' is negative "
                            "(-2); a clocking skew shall be a non-negative "
                            "integer value",
                            6, "14.3"));
}

TEST(ClockingBlockElab, NegativeDefaultInputSkewRejected) {
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." Here the
  // offending delay_control is the input half of a default_skew clocking item.
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
  // Both halves of the default_skew item stand on line 5, so the report names
  // which half it read. The output half of this item is legal and draws
  // nothing.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default input skew is negative (-1); a clocking "
                            "skew shall be a non-negative integer value",
                            5, "14.3"));
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
  // The skew never reaches the non-negative-integer test: a reference to a
  // variable is not a constant expression, and CheckClockingSkew in
  // src/elaborator/elaborator_validate_clocking.cpp reports that under §14.4
  // and returns.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking skew shall be a constant expression", 6,
                            "14.4"));
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
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." Here the
  // offending delay_control is the output half of a default_skew clocking item.
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
  // The input half of this item is legal, so a report naming the output half
  // is what distinguishes this case from
  // ClockingBlockElab.NegativeDefaultInputSkewRejected above, whose source
  // breaks the other half of the same line.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default output skew is negative (-1); a clocking "
                            "skew shall be a non-negative integer value",
                            5, "14.3"));
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
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." A fractional
  // real constant is neither, so it breaks the integer half of the
  // requirement.
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
  // ConstEvalInt does not answer for a real literal, so this source is the one
  // that reaches CheckClockingSkewRealValue in
  // src/elaborator/elaborator_validate_clocking.cpp rather than the integer
  // path of CheckClockingSkew. Naming the integer half and 1.5 is what keeps
  // this case from passing on a negative integer skew.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "input skew of clocking signal 'a' is not an "
                            "integer (1.5); a clocking skew shall be a "
                            "non-negative integer value",
                            5, "14.3"));
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

TEST(ClockingBlockElab, SignalSkewNamesTheSignal) {
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." A block may
  // carry a legal default_skew item and an offending signal skew at once, so
  // the report names the clocking signal whose skew it read.
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
  // The default input skew on line 5 is legal, so naming clocking signal 'a'
  // is what separates the per-signal calls to CheckClockingSkew in
  // src/elaborator/elaborator_validate_clocking.cpp from the two the same
  // function receives for the default_skew item.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking signal 'a' is negative (-1)", 6, "14.3"));
}

TEST(ClockingBlockElab, NonNegativeIntegerSkewStillAccepted) {
  // §14.3: "The delay_control shall be either a time literal or a constant
  // expression that evaluates to a non-negative integer value." A skew that is
  // a non-negative integer satisfies both halves and shall draw no report. The
  // case guards the accepting path against a rejection built into the report:
  // CheckClockingSkew in src/elaborator/elaborator_validate_clocking.cpp reads
  // the folded value to compose its message, and a value read on every skew is
  // a value that can be reported on every skew.
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

}  // namespace
