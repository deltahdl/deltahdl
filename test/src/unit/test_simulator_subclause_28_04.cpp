#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <tuple>
#include <utility>

#include "fixture_simulator.h"
#include "model_gate_logic.h"
#include "model_val4.h"

using namespace delta;

using GateTruthEntry = std::tuple<Val4, Val4, Val4>;

static void RunGateTruthTable(GateKind kind,
                              std::initializer_list<GateTruthEntry> cases,
                              const char* label) {
  for (auto& [a, b, expected] : cases) {
    EXPECT_EQ(EvalNInputGate(kind, a, b), expected)
        << label << " a=" << static_cast<int>(a)
        << " b=" << static_cast<int>(b);
  }
}

namespace {

TEST(LogicGates, AndGateTruthTable) {
  RunGateTruthTable(GateKind::kAnd,
                    {

                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV0},
                        {Val4::kV0, Val4::kX, Val4::kV0},
                        {Val4::kV0, Val4::kZ, Val4::kV0},

                        {Val4::kV1, Val4::kV0, Val4::kV0},
                        {Val4::kV1, Val4::kV1, Val4::kV1},
                        {Val4::kV1, Val4::kX, Val4::kX},
                        {Val4::kV1, Val4::kZ, Val4::kX},

                        {Val4::kX, Val4::kV0, Val4::kV0},
                        {Val4::kX, Val4::kV1, Val4::kX},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},

                        {Val4::kZ, Val4::kV0, Val4::kV0},
                        {Val4::kZ, Val4::kV1, Val4::kX},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "And");
}

TEST(LogicGates, OrGateTruthTable) {
  RunGateTruthTable(GateKind::kOr,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV1},
                        {Val4::kV1, Val4::kX, Val4::kV1},
                        {Val4::kV1, Val4::kZ, Val4::kV1},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kV1},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kV1},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Or");
}

TEST(LogicGates, XorGateTruthTable) {
  RunGateTruthTable(GateKind::kXor,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV0},
                        {Val4::kV1, Val4::kX, Val4::kX},
                        {Val4::kV1, Val4::kZ, Val4::kX},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kX},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kX},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Xor");
}

TEST(LogicGates, NandIsInvertedAnd) {
  CheckInversion(GateKind::kAnd, GateKind::kNand);
}

TEST(LogicGates, NorIsInvertedOr) {
  CheckInversion(GateKind::kOr, GateKind::kNor);
}

TEST(LogicGates, XnorIsInvertedXor) {
  CheckInversion(GateKind::kXor, GateKind::kXnor);
}

TEST(NInputGateDelay, NoDelaySpecYieldsZeroPropagation) {
  static constexpr Val4 kVals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 from : kVals) {
    for (Val4 to : kVals) {
      EXPECT_EQ(ComputeGateDelay(0, 0, from, to), 0u);
    }
  }
}

TEST(NInputGateDelay, SingleDelayDrivesBothRiseAndFall) {
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV0, Val4::kV1), 8u);
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV1, Val4::kV0), 8u);
}

TEST(NInputGateDelay, TwoDelaysSplitRiseAndFall) {
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kV1), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kV0), 9u);
}

TEST(NInputGateDelay, TwoDelaysToXUsesSmaller) {
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV1, Val4::kX), 4u);
}

TEST(LogicGates, ProductionAndGateOutputsConjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b0; end\n"
      "  and g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionNandGateInvertsConjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  nand g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionOrGateOutputsDisjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b1; end\n"
      "  or g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionNorGateInvertsDisjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b0; end\n"
      "  nor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXorGateOutputsParity) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b0; end\n"
      "  xor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXnorGateInvertsParity) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  xnor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionAndGateControllingZeroDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
      "  wire y;\n"
      "  and g(y, a, b);\n"
      "  initial a = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionAndGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
      "  wire y;\n"
      "  and g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(LogicGates, ProductionOrGateControllingOneDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
      "  wire y;\n"
      "  or g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXorGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
      "  wire y;\n"
      "  xor g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(NInputGateDelay, ProductionTwoDelayAndGateFallTransitionUsesSecondSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; #3 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 12u);
}

TEST(NInputGateDelay, ProductionTwoDelayAndGateTransitionToXUsesSmallerSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; #5 b = 1'bx; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 9u);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(NInputGateDelay, ProductionTwoDelayAndGateSchedulerEndsAtInputPlusRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b0; #3 a = 1'b1; b = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

TEST(NInputGateSim, ASingleInputGateDrivesXForAZInput) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire i;\n"
      "  wire oa, oo, ox, on;\n"
      "  and g1 (oa, i);\n"
      "  or  g2 (oo, i);\n"
      "  xor g3 (ox, i);\n"
      "  nand g4 (on, i);\n"
      "  initial #1 $display(\"%b %b %b %b\", oa, oo, ox, on);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x x x x\n");
}

constexpr const char* kLevels[] = {"1'b0", "1'b1", "1'bx", "1'bz"};

std::string TwoInputTableShown(const std::string& gate) {
  std::string src = "module m;\n  logic a, b;\n  wire y;\n  ";
  src += gate;
  src += " g(y, a, b);\n  initial begin\n";
  for (const char* a : kLevels) {
    for (const char* b : kLevels) {
      src += "    a = ";
      src += a;
      src += "; b = ";
      src += b;
      src += "; #1 $write(\"%b\", y);\n";
    }
  }
  src += "    $display;\n  end\nendmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

TEST(NInputGateSim, EveryEntryOfEachTwoInputTable) {
  const std::pair<std::string, std::string> kTables[] = {{"and",
                                                          "0000"
                                                          "01xx"
                                                          "0xxx"
                                                          "0xxx"},
                                                         {"or",
                                                          "01xx"
                                                          "1111"
                                                          "x1xx"
                                                          "x1xx"},
                                                         {"xor",
                                                          "01xx"
                                                          "10xx"
                                                          "xxxx"
                                                          "xxxx"},
                                                         {"nand",
                                                          "1111"
                                                          "10xx"
                                                          "1xxx"
                                                          "1xxx"},
                                                         {"nor",
                                                          "10xx"
                                                          "0000"
                                                          "x0xx"
                                                          "x0xx"},
                                                         {"xnor",
                                                          "10xx"
                                                          "01xx"
                                                          "xxxx"
                                                          "xxxx"}};
  for (const auto& [gate, rows] : kTables) {
    EXPECT_EQ(TwoInputTableShown(gate), rows + "\n") << gate;
  }
}

std::string ManyInputsShown(const std::string& gate,
                            const std::string& inputs) {
  std::string src = "module m;\n  wire y;\n  ";
  src += gate;
  src += " g(y, ";
  src += inputs;
  src += ");\n  initial #1 $display(\"%b\", y);\nendmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

TEST(NInputGateSim, AGateWithThreeOrMoreInputsExtendsItsFunction) {
  const std::tuple<std::string, std::string, std::string> kCases[] = {
      {"xor", "1'b1, 1'b1, 1'b1", "1"},
      {"xor", "1'b1, 1'b1, 1'b1, 1'b1", "0"},
      {"xnor", "1'b1, 1'b1, 1'b1", "0"},
      {"xnor", "1'b1, 1'b1, 1'b1, 1'b1", "1"},
      {"and", "1'b1, 1'bx, 1'b1", "x"},
      {"and", "1'b1, 1'bx, 1'b0", "0"},
      {"and", "1'b1, 1'b1, 1'b1, 1'b1", "1"},
      {"or", "1'b0, 1'bz, 1'b0", "x"},
      {"or", "1'b0, 1'bz, 1'b1", "1"},
      {"or", "1'b0, 1'b0, 1'b0, 1'b0", "0"},
      {"nand", "1'b1, 1'bz, 1'b1", "x"},
      {"nand", "1'bx, 1'b1, 1'b0", "1"},
      {"nor", "1'b0, 1'bx, 1'b0", "x"},
      {"nor", "1'bz, 1'b0, 1'b1", "0"}};
  for (const auto& [gate, inputs, value] : kCases) {
    EXPECT_EQ(ManyInputsShown(gate, inputs), value + "\n")
        << gate << " " << inputs;
  }
}

TEST(NInputGateSim, AnInvertingGateInvertsTheWholeReductionOnce) {
  const std::tuple<std::string, std::string, std::string> kCases[] = {
      {"nand", "1'b1, 1'b1, 1'b1", "0"},
      {"nand", "1'b1, 1'b1, 1'b1, 1'b1", "0"},
      {"nor", "1'b0, 1'b0, 1'b0", "1"},
      {"nor", "1'b0, 1'b0, 1'b0, 1'b0", "1"},
      {"xnor", "1'b1, 1'b1, 1'b1", "0"},
      {"xnor", "1'b0, 1'b1, 1'b1, 1'b1", "0"}};
  for (const auto& [gate, inputs, value] : kCases) {
    EXPECT_EQ(ManyInputsShown(gate, inputs), value + "\n")
        << gate << " " << inputs;
  }
}

std::string TransitionsShown(const std::string& gate, const std::string& delay,
                             int input_count) {
  const bool kHeldHigh = gate == "and" || gate == "nand";
  std::string src = "module m;\n  logic a;\n  wire y;\n  wire k = ";
  src += kHeldHigh ? "1'b1" : "1'b0";
  src += ";\n  ";
  src += gate;
  src += " ";
  src += delay;
  src += " g(y, a";
  for (int i = 1; i < input_count; ++i) src += ", k";
  src +=
      ");\n"
      "  always @(y) $display(\"%0t %b\", $time, y);\n"
      "  initial begin\n"
      "    a = 1'b0; #20 a = 1'b1; #20 a = 1'b0; #20 a = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

constexpr const char* kNInputGates[] = {"and", "nand", "or",
                                        "nor", "xor",  "xnor"};

bool Inverting(const std::string& gate) {
  return gate == "nand" || gate == "nor" || gate == "xnor";
}

TEST(NInputGateDelay, OneDelayTimesEveryOutputTransition) {
  for (const std::string& gate : kNInputGates) {
    EXPECT_EQ(TransitionsShown(gate, "#5", 2), Inverting(gate)
                                                   ? "5 1\n25 0\n45 1\n65 x\n"
                                                   : "5 0\n25 1\n45 0\n65 x\n")
        << gate;
  }
}

TEST(NInputGateDelay, TwoDelaysTimeTheRiseAndTheFall) {
  for (const std::string& gate : kNInputGates) {
    EXPECT_EQ(
        TransitionsShown(gate, "#(4, 9)", 2),
        Inverting(gate) ? "4 1\n29 0\n44 1\n64 x\n" : "9 0\n24 1\n49 0\n64 x\n")
        << gate;
  }
}

TEST(NInputGateDelay, AMoveToXTakesTheSmallerOfTwoDelays) {
  for (const std::string& gate : kNInputGates) {
    EXPECT_EQ(
        TransitionsShown(gate, "#(9, 4)", 2),
        Inverting(gate) ? "9 1\n24 0\n49 1\n64 x\n" : "4 0\n29 1\n44 0\n64 x\n")
        << gate;
  }
}

TEST(NInputGateDelay, EightInputsTakeTheSameDelaysAsTwo) {
  for (const std::string& gate : kNInputGates) {
    for (const std::string& delay : {"#5", "#(4, 9)", "#(9, 4)"}) {
      EXPECT_EQ(TransitionsShown(gate, delay, 8),
                TransitionsShown(gate, delay, 2))
          << gate << " " << delay;
    }
  }
}

}  // namespace
