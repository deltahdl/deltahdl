#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssertionParsing, SampledFunctionInAssert) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, RoseFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastFunctionWithTicks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: number_of_ticks shall be an elaboration-time constant expression. A
// parameter is a constant expression (§11.2.1), a distinct input form from a
// bare literal, and takes a different expression-parse path in the tick-count
// position of $past.
TEST(AssertionParsing, PastTicksAsParameter) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 2;\n"
      "  assert property (@(posedge clk) $past(req, N) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: a localparam is likewise a constant expression (§11.2.1) admitted in
// the number_of_ticks position of $past.
TEST(AssertionParsing, PastTicksAsLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  localparam int K = 3;\n"
      "  assert property (@(posedge clk) $past(req, K) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: when intermediate optional arguments between two arguments are not
// needed, a comma is placed for each omitted argument, e.g. $past(in1, ,
// enable) omits number_of_ticks while supplying expression2.
TEST(AssertionParsing, PastOmittedMiddleArgument) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(in1, , enable) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: the clocking event may be supplied explicitly as an argument to a
// sampled value function, e.g. $rose(req, @(posedge fclk)).
TEST(AssertionParsing, RoseWithExplicitClockingEvent) {
  auto r = Parse(
      "module m;\n"
      "  assert property\n"
      "    (@(posedge clk) en && $rose(req, @(posedge fclk)) |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: the sampled value functions are not limited to assertions; a value
// change function such as $rose may appear as an ordinary expression in
// procedural code.
TEST(AssertionParsing, RoseInProceduralAssignment) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) reg1 <= a & $rose(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.9.3: $past may likewise be used in any SystemVerilog expression, e.g. in
// a procedural nonblocking assignment.
TEST(AssertionParsing, PastInProceduralAssignment) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) reg1 <= a & $past(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
