#include <gtest/gtest.h>

#include <algorithm>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "model_gate_declaration.h"

namespace {

TEST(GateStrengthValidity, StrengthSpecAllowedForNInputGates) {
  constexpr ModelGateType kNInputGates[] = {
      ModelGateType::kAnd, ModelGateType::kNand, ModelGateType::kOr,
      ModelGateType::kNor, ModelGateType::kXor,  ModelGateType::kXnor,
  };
  for (auto gate : kNInputGates) {
    EXPECT_TRUE(CanHaveStrengthSpec(gate));
  }
}

TEST(GateStrengthValidity, StrengthSpecAllowedForEnableGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kBufif0));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kBufif1));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kNotif0));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kNotif1));
}

TEST(GateStrengthValidity, StrengthSpecAllowedForNOutputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kBuf));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kNot));
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
  EXPECT_TRUE(ReportedError(r.diags,
                            "the drive strength comes after the delay here; it "
                            "has to be written first",
                            3, "28.3.2"));
  EXPECT_EQ(std::count_if(r.diags.begin(), r.diags.end(),
                          [](const Diagnostic& d) {
                            return d.severity == DiagSeverity::kError;
                          }),
            1);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 4u);
}

TEST(GateInstStrengthParsing, TerminalListAfterDelayStillParses) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 (y, a, b);\n"
      "endmodule");
  EXPECT_FALSE(r.has_errors);
}

TEST(GateInstStrengthParsing, SingleStrengthRejectedOnNonPullGate) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (strong0) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "drive strength on this gate type requires both a "
                            "strength0 and a strength1 keyword",
                            3, "28.3.2"));
}

TEST(GateInstStrengthParsing, SingleStrength1RejectedOnNonPullGate) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nand (strong1) g(y, a, b);\n"
      "endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "drive strength on this gate type requires both a "
                            "strength0 and a strength1 keyword",
                            3, "28.3.2"));
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
  EXPECT_TRUE(ReportedError(
      r.diags, "pullup single-strength must be a strength1 keyword", 3,
      "28.3.2"));
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
  EXPECT_TRUE(ReportedError(
      r.diags, "pulldown single-strength must be a strength0 keyword", 3,
      "28.3.2"));
}

TEST(SwitchStrengthRejection, NmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, ctrl;\n"
      "  nmos (strong0, strong1) g(y, in, ctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "drive strength not allowed on this gate type", 3, "28.3.2"));
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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got 'strong1'", 3, "28.3.2"));
}

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

TEST(GateInstStrengthParsing, StrengthWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and strong0, strong1 g(y, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got 'strong0'", 3, "28.3.6"));
}

TEST(SwitchStrengthRejection, PmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, ctrl;\n"
      "  pmos (strong0, strong1) g(y, in, ctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "drive strength not allowed on this gate type", 3, "28.3.2"));
}

TEST(SwitchStrengthRejection, CmosStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, in, nc, pc;\n"
      "  cmos (strong0, strong1) g(y, in, nc, pc);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "drive strength not allowed on this gate type", 3, "28.3.2"));
}

TEST(SwitchStrengthRejection, TranStrengthRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (strong0, strong1) g(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "drive strength not allowed on this gate type", 3, "28.3.2"));
}

}  // namespace
