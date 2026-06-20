#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CheckerContextInferenceDefaults) {
  auto* unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      property p(logic sig);
        sig;
      endproperty
      a1: assert property (@clock disable iff (reset) p(test_sig));
    endchecker : check_in_context
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "check_in_context");
  EXPECT_GE(unit->checkers[0]->ports.size(), 3u);
}

TEST_F(VerifyParseTest, CheckerContextInferenceInstantiation) {
  auto* unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      a1: assert property (@clock disable iff (reset) test_sig);
    endchecker : check_in_context
    module m(logic rst);
      wire clk;
      logic a, en;
      wire b = a && en;
      check_in_context my_check1(.test_sig(b), .clock(clk), .reset(rst));
    endmodule : m
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
