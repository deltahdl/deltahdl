#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_ClockingEventPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

TEST(ParserSection16, MultichannelAssertPropertyInline) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, MulticlockPropertyDeclImplication) {
  auto r = Parse(
      "module m;\n"
      "  property p_multi;\n"
      "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
