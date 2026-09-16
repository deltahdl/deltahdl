#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.1: a true property runs the pass statements, a false property runs the
// fail statements, and a disabled property runs no action_block statement.
TEST(AssertStatement, ActionBlockChoiceFollowsPropertyOutcome) {
  EXPECT_EQ(SelectAssertActionBlock(/*property_passed=*/true,
                                    /*property_disabled=*/false),
            AssertActionBlockChoice::kPass);
  EXPECT_EQ(SelectAssertActionBlock(/*property_passed=*/false,
                                    /*property_disabled=*/false),
            AssertActionBlockChoice::kFail);
  EXPECT_EQ(SelectAssertActionBlock(/*property_passed=*/false,
                                    /*property_disabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.1: a disabled evaluation suppresses the action_block even when the
// property would otherwise be considered to pass.
TEST(AssertStatement, DisabledTakesPrecedenceOverPass) {
  EXPECT_EQ(SelectAssertActionBlock(/*property_passed=*/true,
                                    /*property_disabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.1: the pass/fail statements can be controlled by the §20.11 assertion
// action control tasks; a disabled pass or fail action drops the branch.
TEST(AssertStatement, ActionControlSuppressesSelectedBranch) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kPass,
                                            /*pass_action_enabled=*/false,
                                            /*fail_action_enabled=*/true),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kFail,
                                            /*pass_action_enabled=*/true,
                                            /*fail_action_enabled=*/false),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kFail,
                                            /*pass_action_enabled=*/true,
                                            /*fail_action_enabled=*/true),
            AssertActionBlockChoice::kFail);
}

// §16.14.1: with the else clause omitted the tool calls $error on failure,
// unless $assertcontrol (a FailOff) has suppressed the fail action.
TEST(AssertStatement, DefaultErrorOnFailureUnlessSuppressed) {
  DeferredAssertion da;
  da.condition_val = 0;        // the property failed
  da.has_else_clause = false;  // no explicit else action
  EXPECT_TRUE(CallsDefaultErrorOnFailure(da, /*fail_action_enabled=*/true));
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, /*fail_action_enabled=*/false));
}

// §16.14.1: a present else clause supplies the fail action, so the default
// $error is not called.
TEST(AssertStatement, NoDefaultErrorWhenElseClausePresent) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = true;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, /*fail_action_enabled=*/true));
}

// §16.14.1: the default severity of a concurrent assertion action block is
// error, as for immediate assertions.
TEST(AssertStatement, DefaultSeverityIsError) {
  EXPECT_EQ(DefaultConcurrentAssertActionSeverity(), AssertionSeverity::kError);
}

// §16.14.1: the pass and fail statements execute in the Reactive region.
TEST(AssertStatement, ActionExecutesInReactiveRegion) {
  EXPECT_EQ(ConcurrentAssertActionRegion(), Region::kReactive);
}

// §16.14.1: when the §20.11 control leaves the pass action enabled, a passing
// assertion's pass branch survives and its pass statements run.
TEST(AssertStatement, ControlAllowsPassBranchWhenEnabled) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kPass,
                                            /*pass_action_enabled=*/true,
                                            /*fail_action_enabled=*/true),
            AssertActionBlockChoice::kPass);
}

// §16.14.1: a disabled evaluation runs no action_block statement, so the
// action control tasks cannot resurrect a suppressed branch — a kNone choice
// stays kNone regardless of the pass/fail enables.
TEST(AssertStatement, ControlDoesNotResurrectDisabledAction) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kNone,
                                            /*pass_action_enabled=*/true,
                                            /*fail_action_enabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.1: a passing assertion takes the pass branch, never the default
// $error fail action, even with no else clause.
TEST(AssertStatement, NoDefaultErrorWhenPropertyPasses) {
  DeferredAssertion da;
  da.condition_val = 1;  // the property held
  da.has_else_clause = false;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, /*fail_action_enabled=*/true));
}

// §16.14.1: a cover statement has no fail action, so the default $error
// fallback does not apply to it even when it does not hold.
TEST(AssertStatement, NoDefaultErrorForCover) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = false;
  da.kind = AssertionKind::kCover;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, /*fail_action_enabled=*/true));
}

}  // namespace
