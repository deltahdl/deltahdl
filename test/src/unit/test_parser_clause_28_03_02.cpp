// §28.3.2: The drive strength specification

#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

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
  constexpr GateType kNInputGates[] = {
      GateType::kAnd, GateType::kNand, GateType::kOr,
      GateType::kNor, GateType::kXor,  GateType::kXnor,
  };
  for (auto gate : kNInputGates) {
    EXPECT_TRUE(CanHaveStrengthSpec(gate));
  }
}

TEST(GateDecl, StrengthSpecValidForEnableGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif1));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif1));
}

TEST(GateDecl, StrengthSpecValidForNOutputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBuf));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNot));
}

}  // namespace
