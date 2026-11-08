#include <gtest/gtest.h>

#include "fixture_program.h"
#include "parser/ast_expr.h"

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
  ASSERT_EQ(unit->checkers[0]->ports.size(), 3u);

  const auto& ports = unit->checkers[0]->ports;
  EXPECT_EQ(ports[0].name, "test_sig");
  EXPECT_EQ(ports[0].default_value, nullptr);
  ASSERT_NE(ports[1].default_value, nullptr);
  EXPECT_EQ(ports[1].default_value->kind, ExprKind::kSystemCall);
  EXPECT_EQ(ports[1].default_value->callee, "$inferred_clock");
  ASSERT_NE(ports[2].default_value, nullptr);
  EXPECT_EQ(ports[2].default_value->kind, ExprKind::kSystemCall);
  EXPECT_EQ(ports[2].default_value->callee, "$inferred_disable");
}

TEST_F(VerifyParseTest, CheckerContextInferenceOmittedOptionalArgs) {
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
