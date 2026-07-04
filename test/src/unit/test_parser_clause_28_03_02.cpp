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

// §28.3.2 admits every Table 28-2 primitive as a strength carrier. Each gate
// keyword is a distinct case in the allow-list, so drive one instantiation of
// every remaining n-input/n-output/enable gate through a real parse and confirm
// the strengths are accepted and recorded on the instance.
TEST(GateInstStrengthParsing, NorWithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nor (strong0, strong1) g(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(GateInstStrengthParsing, XorWithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor (pull0, weak1) g(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

TEST(GateInstStrengthParsing, XnorWithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xnor (weak0, pull1) g(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(GateInstStrengthParsing, NotWithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  not (strong0, strong1) g(y, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(GateInstStrengthParsing, Bufif0WithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 (strong0, weak1) g(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

TEST(GateInstStrengthParsing, Notif0WithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  notif0 (pull0, strong1) g(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(GateInstStrengthParsing, Notif1WithStrengthAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  notif1 (supply0, supply1) g(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->drive_strength0, 5u);
  EXPECT_EQ(item->drive_strength1, 5u);
}

// §28.3.2 negative form: a strength specification must be enclosed in a pair of
// parentheses; bare strength keywords after the gate type are not accepted.
TEST(GateInstStrengthParsing, StrengthWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and strong0, strong1 g(y, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.3.2 negative form: only Table 28-2 primitives may carry a drive strength.
// nmos is exercised above; cover the other switch families (MOS pmos, CMOS,
// bidirectional tran) each with a full parse that must reject the strength.
TEST(SwitchStrengthRejection, PmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, ctrl;\n"
      "  pmos (strong0, strong1) g(y, in, ctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SwitchStrengthRejection, CmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, nc, pc;\n"
      "  cmos (strong0, strong1) g(y, in, nc, pc);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SwitchStrengthRejection, TranStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (strong0, strong1) g(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
