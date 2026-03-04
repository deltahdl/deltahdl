// §10.6.2: The force and release procedural statements

#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "helpers_force_target.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;
namespace {

TEST(ForceRelease, LegalTargetNet) {
  ForceInfo info{ForceTarget::kNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConcatenation) {
  ForceInfo info{ForceTarget::kConcatenation};
  EXPECT_TRUE(ValidateForceTarget(info));
}

// --- Illegal LHS targets ---
// §10.6.2:
TEST(ForceRelease, IllegalBitSelectVariable) {
  ForceInfo info{ForceTarget::kBitSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalPartSelectVariable) {
  ForceInfo info{ForceTarget::kPartSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

// §10.6.2: "A force or release statement shall not be applied to a
//  variable that is being assigned by a mixture of continuous and
//  procedural assignments."
TEST(ForceRelease, IllegalMixedAssignmentTarget) {
  ForceInfo info{ForceTarget::kSingularVariable};
  info.has_mixed_assignments = true;
  EXPECT_FALSE(ValidateForceTarget(info));
}

}  // namespace
