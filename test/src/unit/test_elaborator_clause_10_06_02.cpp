// §10.6.2: The force and release procedural statements

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// --- Local types for force/release (§10.6.2) ---
enum class ForceTarget : uint8_t {
  kSingularVariable,
  kNet,
  kConstBitSelectNet,
  kConstPartSelectNet,
  kConcatenation,
  kBitSelectVariable,
  kPartSelectVariable,
  kUserDefinedNettypePartSelect,
};

struct ForceInfo {
  ForceTarget target;
  bool has_mixed_assignments = false;
};

bool ValidateForceTarget(const ForceInfo& info) {
  if (info.has_mixed_assignments) return false;
  switch (info.target) {
    case ForceTarget::kSingularVariable:
    case ForceTarget::kNet:
    case ForceTarget::kConstBitSelectNet:
    case ForceTarget::kConstPartSelectNet:
    case ForceTarget::kConcatenation:
      return true;
    case ForceTarget::kBitSelectVariable:
    case ForceTarget::kPartSelectVariable:
    case ForceTarget::kUserDefinedNettypePartSelect:
      return false;
  }
  return false;
}

static constexpr uint8_t kVal0 = 0;

static constexpr uint8_t kVal1 = 1;

namespace {

TEST(ForceRelease, LegalTargetNet) {
  ForceInfo info{ForceTarget::kNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConcatenation) {
  ForceInfo info{ForceTarget::kConcatenation};
  EXPECT_TRUE(ValidateForceTarget(info));
}

}  // namespace
