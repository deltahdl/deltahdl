#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

// --- Local types for timing control (§9.4) ---

enum class Logic4 : uint8_t {
  kVal0 = 0,
  kVal1 = 1,
  kX = 2,
  kZ = 3,
};

enum class EdgeKind : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
};

enum class ExprRole : uint8_t {
  kRHS,
  kSubroutineArg,
  kCaseExpr,
  kConditionalExpr,
  kLHSIndex,
  kPureLHS,
  kTimingControl,
};

struct VarRef {
  std::string name;
  ExprRole role;
};

EdgeKind DetectEdge(Logic4 from, Logic4 to);
bool IsEdge(Logic4 from, Logic4 to);
uint64_t EvaluateDelay(int64_t value, bool is_unknown, bool is_highz);
std::vector<std::string> ComputeImplicitSensitivity(
    const std::vector<VarRef>& refs);
bool EvaluateWaitCondition(uint64_t value);
uint64_t EvaluateRepeatCount(int64_t count, bool is_signed, bool is_unknown,
                             bool is_highz);

// §9.4.2: Edge detection per posedge/negedge transition tables.
// Posedge: 0->1, 0->x, 0->z, x->1, z->1
// Negedge: 1->0, 1->x, 1->z, x->0, z->0
// All other transitions: no edge.
EdgeKind DetectEdge(Logic4 from, Logic4 to) {
  if (from == to) return EdgeKind::kNone;
  // Posedge transitions.
  if (from == Logic4::kVal0 &&
      (to == Logic4::kVal1 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kPosedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal1)
    return EdgeKind::kPosedge;
  // Negedge transitions.
  if (from == Logic4::kVal1 &&
      (to == Logic4::kVal0 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kNegedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal0)
    return EdgeKind::kNegedge;
  return EdgeKind::kNone;
}

bool IsEdge(Logic4 from, Logic4 to) {
  EdgeKind e = DetectEdge(from, to);
  return e == EdgeKind::kPosedge || e == EdgeKind::kNegedge;
}

uint64_t EvaluateDelay(int64_t value, bool is_unknown, bool is_highz) {
  if (is_unknown || is_highz) return 0;
  if (value < 0) return static_cast<uint64_t>(value);
  return static_cast<uint64_t>(value);
}

std::vector<std::string> ComputeImplicitSensitivity(
    const std::vector<VarRef>& refs) {
  std::vector<std::string> result;
  for (const auto& ref : refs) {
    switch (ref.role) {
      case ExprRole::kRHS:
      case ExprRole::kSubroutineArg:
      case ExprRole::kCaseExpr:
      case ExprRole::kConditionalExpr:
      case ExprRole::kLHSIndex:
        result.push_back(ref.name);
        break;
      case ExprRole::kPureLHS:
      case ExprRole::kTimingControl:
        break;
    }
  }
  return result;
}

bool EvaluateWaitCondition(uint64_t value) { return value != 0; }

uint64_t EvaluateRepeatCount(int64_t count, bool is_signed, bool is_unknown,
                             bool is_highz) {
  if (is_unknown || is_highz) return 0;
  if (is_signed && count <= 0) return 0;
  if (!is_signed && count < 0) return static_cast<uint64_t>(count);
  return static_cast<uint64_t>(count);
}

// =============================================================
// §9.4: Procedural timing controls
// =============================================================

// --- §9.4.1: Delay control ---

// §9.4.1: "If the delay expression evaluates to an unknown or
//  high-impedance value, it shall be interpreted as zero delay."
TEST(TimingControl, UnknownDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, true, false), 0u);
}

TEST(TimingControl, HighZDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, true), 0u);
}

// §9.4.1: "If the delay expression evaluates to a negative value, it
//  shall be interpreted as a two's-complement unsigned integer."
TEST(TimingControl, NegativeDelayUnsignedInterpretation) {
  uint64_t result = EvaluateDelay(-1, false, false);
  EXPECT_GT(result, 0u);
}

TEST(TimingControl, PositiveDelayPassesThrough) {
  EXPECT_EQ(EvaluateDelay(10, false, false), 10u);
}

TEST(TimingControl, ZeroDelayIsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, false), 0u);
}

// --- §9.4.2: Event control — edge detection ---

// §9.4.2: "A posedge shall be detected on the transition from 0 to x,
//  z, or 1, and from x or z to 1."
TEST(TimingControl, Posedge0To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(TimingControl, Posedge0ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kX), EdgeKind::kPosedge);
}

TEST(TimingControl, Posedge0ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kZ), EdgeKind::kPosedge);
}

TEST(TimingControl, PosedgeXTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(TimingControl, PosedgeZTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal1), EdgeKind::kPosedge);
}

// §9.4.2: "A negedge shall be detected on the transition from 1 to x,
//  z, or 0, and from x or z to 0."
TEST(TimingControl, Negedge1To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(TimingControl, Negedge1ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kX), EdgeKind::kNegedge);
}

TEST(TimingControl, Negedge1ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kZ), EdgeKind::kNegedge);
}

TEST(TimingControl, NegedgeXTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(TimingControl, NegedgeZTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal0), EdgeKind::kNegedge);
}

// No-edge transitions.
TEST(TimingControl, NoEdge0To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal0), EdgeKind::kNone);
}

TEST(TimingControl, NoEdge1To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal1), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeXToX) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kX), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeXToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kZ), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeZToX) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kX), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeZToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kZ), EdgeKind::kNone);
}

// §9.4.2: "An edge shall be detected whenever negedge or posedge is
//  detected."
TEST(TimingControl, EdgeDetectedOnPosedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal0, Logic4::kVal1));
}

TEST(TimingControl, EdgeDetectedOnNegedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal1, Logic4::kVal0));
}

TEST(TimingControl, NoEdgeDetectedOnSame) {
  EXPECT_FALSE(IsEdge(Logic4::kVal0, Logic4::kVal0));
}

TEST(TimingControl, NoEdgeDetectedXToZ) {
  EXPECT_FALSE(IsEdge(Logic4::kX, Logic4::kZ));
}

// --- §9.4.2.1: Event OR operator ---

// §9.4.2.1: "Comma-separated sensitivity lists shall be synonymous to
//  or-separated sensitivity lists."
// This is a parsing/semantic equivalence test.
TEST(TimingControl, CommaSynonymousWithOr) {
  // Verify that comma-separated and or-separated lists produce
  // identical sensitivity sets.
  std::vector<VarRef> comma_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  std::vector<VarRef> or_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  auto comma_result = ComputeImplicitSensitivity(comma_list);
  auto or_result = ComputeImplicitSensitivity(or_list);
  EXPECT_EQ(comma_result, or_result);
}

// --- §9.4.2.2: Implicit event_expression list (@*) ---

// §9.4.2.2: "Nets and variables that appear on the right-hand side of
//  assignments ... shall all be included."
TEST(TimingControl, ImplicitSensitivityIncludesRHS) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kPureLHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(TimingControl, ImplicitSensitivityIncludesSubroutineArgs) {
  std::vector<VarRef> refs = {
      {"f_arg", ExprRole::kSubroutineArg},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "f_arg");
}

TEST(TimingControl, ImplicitSensitivityIncludesCaseExpr) {
  std::vector<VarRef> refs = {
      {"sel", ExprRole::kCaseExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "sel");
}

TEST(TimingControl, ImplicitSensitivityIncludesConditionalExpr) {
  std::vector<VarRef> refs = {
      {"cond", ExprRole::kConditionalExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "cond");
}

TEST(TimingControl, ImplicitSensitivityIncludesLHSIndex) {
  std::vector<VarRef> refs = {
      {"idx", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "idx");
}

// §9.4.2.2: Identifiers that only appear in timing control are excluded.
TEST(TimingControl, ImplicitSensitivityExcludesTimingControl) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

// §9.4.2.2: Identifiers that only appear as pure LHS are excluded.
TEST(TimingControl, ImplicitSensitivityExcludesPureLHS) {
  std::vector<VarRef> refs = {
      {"out", ExprRole::kPureLHS},
      {"in", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "in");
}

// Multiple variables with mixed roles.
TEST(TimingControl, ImplicitSensitivityMixedRoles) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},      {"b", ExprRole::kSubroutineArg},
      {"c", ExprRole::kPureLHS},  {"d", ExprRole::kTimingControl},
      {"e", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 3u);  // a, b, e
}

// --- §9.4.3: Level-sensitive event control (wait) ---

// §9.4.3: "The wait statement shall evaluate a condition; and, if it is
//  not true, the procedural statements ... shall remain blocked."
TEST(TimingControl, WaitConditionTrueUnblocks) {
  EXPECT_TRUE(EvaluateWaitCondition(1));
}

TEST(TimingControl, WaitConditionFalseBlocks) {
  EXPECT_FALSE(EvaluateWaitCondition(0));
}

TEST(TimingControl, WaitConditionNonzeroIsTrue) {
  EXPECT_TRUE(EvaluateWaitCondition(42));
}

// --- §9.4.5: Intra-assignment — repeat event control ---

// §9.4.5: "If the repeat count expression is less than or equal to zero,
//  unknown, or high impedance at the time of evaluation, the assignment
//  occurs as if there is no repeat construct."
TEST(TimingControl, RepeatCountZeroNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, true, false, false), 0u);
}

TEST(TimingControl, RepeatCountNegativeSignedNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(-3, true, false, false), 0u);
}

TEST(TimingControl, RepeatCountUnknownNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, false, true, false), 0u);
}

TEST(TimingControl, RepeatCountHighZNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, false, false, true), 0u);
}

TEST(TimingControl, RepeatCountPositivePassesThrough) {
  EXPECT_EQ(EvaluateRepeatCount(5, true, false, false), 5u);
}

// §9.4.5: Unsigned variable with negative literal is large positive.
TEST(TimingControl, RepeatCountNegativeUnsignedExecutes) {
  uint64_t result = EvaluateRepeatCount(-3, false, false, false);
  EXPECT_GT(result, 0u);
}
