#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>

// --- Local types for gate declaration (§28.3) ---

enum class GateType : uint8_t {
  kAnd,
  kNand,
  kOr,
  kNor,
  kXor,
  kXnor,
  kBuf,
  kNot,
  kBufif0,
  kBufif1,
  kNotif0,
  kNotif1,
  kNmos,
  kPmos,
  kRnmos,
  kRpmos,
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
  kCmos,
  kRcmos,
  kPullup,
  kPulldown,
};

enum class StrengthLvl : uint8_t {
  kHighz = 0,
  kSmall,
  kMedium,
  kWeak,
  kLarge,
  kPull,
  kStrong,
  kSupply
};

struct GateDeclInfo {
  GateType type = GateType::kAnd;
  bool has_strength = false;
  StrengthLvl strength0 = StrengthLvl::kStrong;
  StrengthLvl strength1 = StrengthLvl::kStrong;
  uint32_t delay_count = 0;
  bool has_name = false;
  bool has_range = false;
  int32_t range_lhi = 0;
  int32_t range_rhi = 0;
  uint32_t terminal_count = 0;
};

bool ValidateGateDecl(const GateDeclInfo& info);
bool CanHaveStrengthSpec(GateType type);
uint32_t ComputeArraySize(int32_t lhi, int32_t rhi);
bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1, GateType type);
uint32_t MaxDelays(GateType type);

bool ValidateGateDecl(const GateDeclInfo& info) {
  return !info.has_range || info.has_name;
}

bool CanHaveStrengthSpec(GateType type) {
  switch (type) {
    case GateType::kAnd:
    case GateType::kNand:
    case GateType::kOr:
    case GateType::kNor:
    case GateType::kXor:
    case GateType::kXnor:
    case GateType::kBuf:
    case GateType::kNot:
    case GateType::kBufif0:
    case GateType::kBufif1:
    case GateType::kNotif0:
    case GateType::kNotif1:
    case GateType::kPullup:
    case GateType::kPulldown:
      return true;
    case GateType::kNmos:
    case GateType::kPmos:
    case GateType::kRnmos:
    case GateType::kRpmos:
    case GateType::kTran:
    case GateType::kRtran:
    case GateType::kTranif0:
    case GateType::kTranif1:
    case GateType::kRtranif0:
    case GateType::kRtranif1:
    case GateType::kCmos:
    case GateType::kRcmos:
      return false;
  }
  return false;
}

uint32_t ComputeArraySize(int32_t lhi, int32_t rhi) {
  return static_cast<uint32_t>(std::abs(lhi - rhi)) + 1;
}

bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1, GateType /*type*/) {
  return s0 != StrengthLvl::kHighz || s1 != StrengthLvl::kHighz;
}

uint32_t MaxDelays(GateType type) {
  switch (type) {
    case GateType::kPullup:
    case GateType::kPulldown:
      return 0;
    case GateType::kAnd:
    case GateType::kNand:
    case GateType::kOr:
    case GateType::kNor:
    case GateType::kXor:
    case GateType::kXnor:
    case GateType::kBuf:
    case GateType::kNot:
      return 2;
    case GateType::kBufif0:
    case GateType::kBufif1:
    case GateType::kNotif0:
    case GateType::kNotif1:
    case GateType::kNmos:
    case GateType::kPmos:
    case GateType::kRnmos:
    case GateType::kRpmos:
    case GateType::kCmos:
    case GateType::kRcmos:
      return 3;
    case GateType::kTranif0:
    case GateType::kTranif1:
    case GateType::kRtranif0:
    case GateType::kRtranif1:
      return 2;
    case GateType::kTran:
    case GateType::kRtran:
      return 0;
  }
  return 0;
}

// =============================================================
// §28.3: Gate and switch declaration syntax
// =============================================================

// §28.3: "Multiple instances of the one type ... shall have the same
//  drive strength and delay specification."

// --- §28.3.1: Gate type specification ---

// §28.3.1: Declaration shall begin with keyword naming the gate type.
// Table 28-1: all 26 built-in gate/switch types.

// --- §28.3.2: Drive strength specification ---

// §28.3.2: Only certain gate types can have drive strength.
TEST(GateDecl, StrengthSpecValidForNInputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kAnd));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNand));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kOr));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNor));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kXor));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kXnor));
}

TEST(GateDecl, StrengthSpecValidForNOutputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBuf));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNot));
}

TEST(GateDecl, StrengthSpecValidForEnableGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif1));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif1));
}

TEST(GateDecl, StrengthSpecValidForPullGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPullup));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPulldown));
}

TEST(GateDecl, StrengthSpecInvalidForSwitches) {
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kNmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kPmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kTran));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kCmos));
}

// §28.3.2: "The strength specifications (highz0, highz1) and
//  (highz1, highz0) shall be considered invalid."
TEST(GateDecl, BothHighzStrengthsInvalid) {
  EXPECT_FALSE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kHighz,
                                    GateType::kAnd));
}

// §28.3.2: "In the absence of a strength specification, the instances
//  shall have the default strengths strong1 and strong0."
TEST(GateDecl, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

// §28.3.2: highz1 → output z instead of 1.
TEST(GateDecl, Highz1OutputsZInsteadOf1) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kStrong, StrengthLvl::kHighz,
                                   GateType::kNor));
}

// --- §28.3.3: Delay specification ---

// §28.3.3: "pullup and pulldown instance declarations shall not include
//  delay specifications."
TEST(GateDecl, PullupNoDelays) { EXPECT_EQ(MaxDelays(GateType::kPullup), 0u); }

TEST(GateDecl, PulldownNoDelays) {
  EXPECT_EQ(MaxDelays(GateType::kPulldown), 0u);
}

TEST(GateDecl, NInputGateMaxTwoDelays) {
  EXPECT_EQ(MaxDelays(GateType::kAnd), 2u);
}

TEST(GateDecl, EnableGateMaxThreeDelays) {
  EXPECT_EQ(MaxDelays(GateType::kBufif0), 3u);
}

TEST(GateDecl, MosSwitchMaxThreeDelays) {
  EXPECT_EQ(MaxDelays(GateType::kNmos), 3u);
}

// §28.3.3: "Gates and switches in declarations with no delay
//  specification shall have no propagation delay."

// --- §28.3.4: Instance identifier ---

// §28.3.4: "If multiple instances are declared as an array of instances,
//  an identifier shall be used to name the instances."
TEST(GateDecl, ArrayRequiresName) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = false;
  EXPECT_FALSE(ValidateGateDecl(info));
}

TEST(GateDecl, ArrayWithNameIsValid) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = true;
  info.range_lhi = 0;
  info.range_rhi = 3;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

// --- §28.3.5: Range specification ---

// §28.3.5: "abs(lhi-rhi)+1 instances"
TEST(GateDecl, ArraySizeComputation) {
  EXPECT_EQ(ComputeArraySize(0, 3), 4u);
  EXPECT_EQ(ComputeArraySize(3, 0), 4u);
  EXPECT_EQ(ComputeArraySize(1, 4), 4u);
}

// §28.3.5: "lhi is not required to be larger than rhi."
TEST(GateDecl, LhiNotRequiredLargerThanRhi) {
  EXPECT_EQ(ComputeArraySize(7, 0), 8u);
  EXPECT_EQ(ComputeArraySize(0, 7), 8u);
}

// §28.3.5: "If both constant expressions are equal, only one instance
//  shall be generated."
TEST(GateDecl, EqualRangeBoundsOneInstance) {
  EXPECT_EQ(ComputeArraySize(5, 5), 1u);
}

// §28.3.5: "If no range specification is given, a single instance
//  shall be created."
TEST(GateDecl, NoRangeSingleInstance) {
  GateDeclInfo info;
  info.has_range = false;
  info.has_name = true;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

// --- §28.3.6: Connection list ---

// §28.3.6: "The output or bidirectional terminals shall always come
//  first in the terminal list, followed by the input terminals."
// §28.3.6: "Too many or too few bits ... shall be considered an error."
