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
  // A.3.2: pullup_strength is (strength0, strength1) | (strength1, strength0) |
  // (strength1); a lone strength is permitted only as a strength1. A single
  // strength0 on a pullup is therefore the wrong strength type. (The two-value
  // (strong0, strong1) form is legal, so it is not the error case.)
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0) (net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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

TEST(GateInstStrengthParsing, DelayBeforeStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 (strong0, strong1) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

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

TEST(PullupStrengthForms, NoStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pullup pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PullupStrengthForms, OnlyStrength1Accepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pullup (strong1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PullupStrengthForms, BothStrengthsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pullup (weak0, strong1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PullupStrengthForms, OnlyStrength0Rejected) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pullup (strong0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PulldownStrengthForms, NoStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pulldown pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PulldownStrengthForms, OnlyStrength0Accepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pulldown (strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PulldownStrengthForms, BothStrengthsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pulldown (strong0, weak1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PulldownStrengthForms, OnlyStrength1Rejected) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  pulldown (strong1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SwitchStrengthRejection, NmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, ctrl;\n"
      "  nmos (strong0, strong1) g(y, in, ctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateInstStrengthParsing, BufWithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  buf (pull0, supply1) g(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 5u);
}

TEST(GateInstStrengthParsing, Bufif1WithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif1 (weak0, strong1) g(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(GateInstStrengthParsing, MissingCommaBetweenStrengthsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (strong0 strong1) g(y, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
