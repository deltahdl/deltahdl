#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(ParserSection40, CoverageControlInAlwaysBlock) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset) begin
          $coverage_control(2, 0, 0);
        end
      end
    endmodule
  )"));
}

}
