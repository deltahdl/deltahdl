#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
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

TEST(CheckerContextDefault, DISABLED_APartOfACheckerFormalsDefaultIsReported) {
  for (const char* formal : {"logic r = $inferred_disable || sig",
                             "untyped clock = $inferred_clock or sig",
                             "untyped clock = $inferred_clock ##1 sig"}) {
    SCOPED_TRACE(formal);
    auto r = Parse("checker c(logic sig,\n  " + std::string(formal) +
                   ");\nendchecker\n");
    EXPECT_TRUE(ReportedError(r.diags,
                              "an inferred clocking or disable function must "
                              "be the entire default value of a formal "
                              "argument",
                              2, "16.14.7"));
  }
}

TEST(CheckerContextDefault, AWholeCheckerFormalDefaultIsAccepted) {
  auto r = Parse(
      "checker c(logic sig,\n"
      "  untyped clock = $inferred_clock,\n"
      "  logic r = $inferred_disable);\n"
      "endchecker\n");
  EXPECT_FALSE(ErrorOnLine(r.diags, 2));
  EXPECT_FALSE(ErrorOnLine(r.diags, 3));
}

}  // namespace
