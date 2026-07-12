#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CheckerContextInferenceDefaults) {
  // §17.4: a context value function may serve as the default value of a checker
  // formal argument. Observe that the parser actually captures each context
  // value function as the corresponding formal's default expression — not
  // merely that the checker parses — while a plain formal keeps no default,
  // which is the contrast shape the rule does not turn into an inferred
  // default.
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
  ASSERT_EQ(unit->checkers[0]->ports.size(), 3u);

  const auto& ports = unit->checkers[0]->ports;
  // test_sig has no default; it is not a context-inferred formal.
  EXPECT_EQ(ports[0].name, "test_sig");
  EXPECT_EQ(ports[0].default_value, nullptr);
  // clock defaults to the $inferred_clock context value function.
  ASSERT_NE(ports[1].default_value, nullptr);
  EXPECT_EQ(ports[1].default_value->kind, ExprKind::kSystemCall);
  EXPECT_EQ(ports[1].default_value->callee, "$inferred_clock");
  // reset defaults to the $inferred_disable context value function.
  ASSERT_NE(ports[2].default_value, nullptr);
  EXPECT_EQ(ports[2].default_value->kind, ExprKind::kSystemCall);
  EXPECT_EQ(ports[2].default_value->callee, "$inferred_disable");
}

TEST_F(VerifyParseTest, CheckerContextInferenceOmittedOptionalArgs) {
  // §17.4 (the my_check2 form): a checker whose optional clock and reset
  // formals carry context value function defaults may be instantiated with
  // those arguments omitted, leaving only the required argument connected. The
  // parser must accept this shorter instantiation — the case where the omitted
  // defaults are the ones later inferred from the instantiation context.
  auto* unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      a1: assert property (@clock disable iff (reset) test_sig);
    endchecker : check_in_context
    module m(logic a);
      check_in_context my_check2(a);
    endmodule : m
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
}

}  // namespace
