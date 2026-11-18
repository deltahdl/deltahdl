#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "model_gate_declaration.h"
#include "parser/ast_expr.h"

namespace {

TEST(GateStrengthValidity, StrengthSpecAllowedForPullGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kPullup));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kPulldown));
}

TEST(GateStrengthValidity, StrengthSpecDisallowedForSwitches) {
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kNmos));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kPmos));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kTran));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kCmos));
}

TEST(GateStrengthValidity, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

TEST(GateElaboration, GateWithStrengthStillProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

TEST(GateElaboration, HighzBothStrengthsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(GateElaboration, HighzBothStrengthsRejectedReversedOrder) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(GateElaboration, DriveStrengthPropagatedToContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  EXPECT_EQ(ca.drive_strength0, 4u);
  EXPECT_EQ(ca.drive_strength1, 1u);
}

constexpr const char* kHighzPair = "drive strength (highz0, highz1) is illegal";
constexpr const char* kBothOrders[] = {"(highz0, highz1)", "(highz1, highz0)"};

bool HighzPairReported(const std::string& src, int line) {
  ElabFixture f;
  Elaborate(src, f);
  return ReportedError(f.diag.Diagnostics(), kHighzPair, line, "28.3.2");
}

bool AcceptedWithoutError(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f);
  return !f.has_errors;
}

std::string InElement(const std::string& element, const std::string& body) {
  return element + " e;\n" + body + "end" + element + "\n";
}

TEST(HighzStrengthPair, EachEnableGateRejectsBothOrders) {
  for (const std::string& gate : {"bufif0", "bufif1", "notif0", "notif1"}) {
    for (const std::string& pair : kBothOrders) {
      std::string src = "module m;\n  wire y, a, c;\n  ";
      src += gate;
      src += " ";
      src += pair;
      src += " g(y, a, c);\nendmodule\n";
      EXPECT_TRUE(HighzPairReported(src, 3)) << gate << " " << pair;
    }
    EXPECT_TRUE(
        AcceptedWithoutError("module m;\n"
                             "  wire y, a, c;\n"
                             "  " +
                             gate +
                             " (highz0, strong1) g(y, a, c);\n"
                             "endmodule\n"))
        << gate;
  }
}

TEST(HighzStrengthPair, AGateInAGenerateBlockRejectsBothOrders) {
  for (const std::string& pair : kBothOrders) {
    EXPECT_TRUE(
        HighzPairReported("module m;\n"
                          "  wire y, a;\n"
                          "  if (1) begin\n"
                          "    buf " +
                              pair +
                              " g(y, a);\n"
                              "  end\n"
                              "endmodule\n",
                          4))
        << pair;
  }
}

TEST(HighzStrengthPair, AUdpInstanceRejectsBothOrders) {
  const std::string kUdp =
      "primitive u(output y, input a);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n";
  for (const std::string& pair : kBothOrders) {
    std::string src = kUdp;
    src += "module m;\n  wire y, a;\n  u ";
    src += pair;
    src += " i(y, a);\nendmodule\n";
    EXPECT_TRUE(HighzPairReported(src, 6)) << pair;
  }
  EXPECT_TRUE(AcceptedWithoutError(kUdp + "module m;\n"
                                          "  wire y, a;\n"
                                          "  u (highz1, weak0) i(y, a);\n"
                                          "endmodule\n"));
}

TEST(HighzStrengthPair, AContinuousAssignmentInEachElementRejectsBothOrders) {
  for (const std::string& element : {"interface", "program"}) {
    for (const std::string& pair : kBothOrders) {
      EXPECT_TRUE(HighzPairReported(InElement(element,
                                              "  wire y;\n"
                                              "  assign " +
                                                  pair + " y = 1'b1;\n") +
                                        "module m;\n  e u();\nendmodule\n",
                                    3))
          << element << " " << pair;
    }
    EXPECT_TRUE(
        AcceptedWithoutError(InElement(element,
                                       "  wire y;\n"
                                       "  assign (highz0, weak1) y = 1'b1;\n") +
                             "module m;\n  e u();\nendmodule\n"))
        << element;
  }
}

TEST(HighzStrengthPair, ANetDeclarationAssignmentOfEachNetTypeRejectsBoth) {
  for (const std::string& net : {"wand", "trireg"}) {
    for (const std::string& pair : kBothOrders) {
      std::string src = "module m;\n  ";
      src += net;
      src += " ";
      src += pair;
      src += " w = 1'b1;\nendmodule\n";
      EXPECT_TRUE(HighzPairReported(src, 2)) << net << " " << pair;
    }
    EXPECT_TRUE(
        AcceptedWithoutError("module m;\n"
                             "  " +
                             net +
                             " (highz0, pull1) w = 1'b1;\n"
                             "endmodule\n"))
        << net;
  }
}

TEST(HighzStrengthPair, ANetDeclarationAssignmentInAnInterfaceRejectsBoth) {
  for (const std::string& pair : kBothOrders) {
    EXPECT_TRUE(HighzPairReported(
        InElement("interface", "  wire " + pair + " w = 1'b1;\n") +
            "module m;\n  e u();\nendmodule\n",
        2))
        << pair;
  }
  EXPECT_TRUE(AcceptedWithoutError(
      InElement("interface", "  wire (highz1, strong0) w = 1'b0;\n") +
      "module m;\n  e u();\nendmodule\n"));
}

}  // namespace
