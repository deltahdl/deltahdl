#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.4: a restrict property statement has the same semantics as assume
// property — it constrains the design and prunes the explored state space the
// same way — so for formal analysis the two are interchangeable.
TEST(RestrictStatement, SharesAssumeConstraintSemantics) {
  EXPECT_TRUE(RestrictSharesAssumeConstraintSemantics());
}

// §16.14.4: in contrast to assume property, a restrict property statement is
// not verified in simulation, so no pass/fail evaluation runs for it.
TEST(RestrictStatement, NotVerifiedInSimulation) {
  EXPECT_FALSE(RestrictIsVerifiedInSimulation());
}

// §16.14.4: because the statement is not verified in simulation, a cycle in
// which the restricted property does not hold — e.g. the example's ctr taking
// value 1 — is not flagged as an error.
TEST(RestrictStatement, ViolationDuringSimulationIsNotAnError) {
  EXPECT_FALSE(RestrictViolationIsSimulationError());
}

}  // namespace
