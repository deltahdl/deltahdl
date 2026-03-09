#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection16, SampledFunctionInAssert) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, RoseFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, FellFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $fell(req) |-> ##1 !ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, StableFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $stable(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PastFunctionWithTicks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, ChangedFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $changed(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
