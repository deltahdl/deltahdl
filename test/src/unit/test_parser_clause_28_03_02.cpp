#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "model_gate_declaration.h"

namespace {

TEST(GateStrengthValidity, StrengthSpecAllowedForNInputGates) {
  constexpr GateType kNInputGates[] = {
      GateType::kAnd, GateType::kNand, GateType::kOr,
      GateType::kNor, GateType::kXor,  GateType::kXnor,
  };
  for (auto gate : kNInputGates) {
    EXPECT_TRUE(CanHaveStrengthSpec(gate));
  }
}

TEST(GateStrengthValidity, StrengthSpecAllowedForEnableGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif1));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif1));
}

TEST(GateStrengthValidity, StrengthSpecAllowedForNOutputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBuf));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNot));
}

TEST(PullGateStrength, StrengthWrongType) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, strong1) (net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// strength0 keyword encoding on a gate instance, paired with a strength1.
TEST(GateInstStrengthParsing, Strength0Strength1KeywordEncoding) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (strong0, weak1) g(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

// The strength specification must parse before the delay specification.
TEST(GateInstStrengthParsing, StrengthPrecedesDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (strong0, strong1) #5 g(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
}

// Writing the delay before the strength violates the mandated ordering.
TEST(GateInstStrengthParsing, DelayBeforeStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 (strong0, strong1) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

// Non-pullup/pulldown gates require both a strength0 and a strength1 keyword;
// a single-strength form is only permitted for pullup/pulldown.
TEST(GateInstStrengthParsing, SingleStrengthRejectedOnNonPullGate) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (strong0) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateInstStrengthParsing, SingleStrength1RejectedOnNonPullGate) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nand (strong1) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

// strength1 may appear before strength0; the encoding must still be correct.
TEST(GateInstStrengthParsing, Strength1BeforeStrength0Encoding) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  or (pull1, weak0) g(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

}  // namespace
