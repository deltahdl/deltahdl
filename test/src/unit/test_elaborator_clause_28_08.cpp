// §28.8

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Bidirectional pass switches must not lower to a continuous assignment —
// they have no unique driven terminal from which to drive the other.
TEST(GateElaboration, TranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, RtranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  rtran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Tranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Tranif1EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif1EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

// Resistive bidirectional terminal restriction: scalar nets are accepted.
TEST(BidirectionalSwitchTerminals, RtranAcceptsScalarNets) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Resistive bidirectional terminal restriction: bit-selects of vector nets
// are accepted.
TEST(BidirectionalSwitchTerminals, RtranAcceptsBitSelectOfVector) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec[2], b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Resistive bidirectional terminal restriction: whole vector net rejected.
TEST(BidirectionalSwitchTerminals, RtranRejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Resistive bidirectional terminal restriction: part-select rejected.
TEST(BidirectionalSwitchTerminals, RtranRejectsPartSelect) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec[1:0], b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, Rtranif0RejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif0 r1(vec, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsPartSelect) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif1 r1(b, vec[3:1], en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The resistive variants do not get the user-defined-net-type carve-out that
// tran/tranif* enjoy, so a rtran whose terminals are UDNT nets must be
// rejected — even when the UDNT is scalar and would otherwise satisfy the
// scalar/bit-select rule.
TEST(BidirectionalSwitchTerminals, RtranRejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, Rtranif0RejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Non-resistive bidirectional switches are not subject to the scalar/bit-select
// rule and may connect whole vector nets.
TEST(BidirectionalSwitchTerminals, TranAcceptsWholeVector) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// UDNT mixing rule: same UDNT on both bidirectional terminals is allowed.
TEST(BidirectionalSwitchUdnt, TranAcceptsSameUdntOnBothSides) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// UDNT mixing rule: a UDNT terminal cannot be connected to a built-in net
// terminal.
TEST(BidirectionalSwitchUdnt, TranRejectsUdntWithBuiltin) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a;\n"
      "  wire b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// UDNT mixing rule: terminals connected to two different UDNTs are rejected.
TEST(BidirectionalSwitchUdnt, TranRejectsDifferentUdnts) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic net_a;\n"
      "  nettype logic net_b;\n"
      "  net_a a;\n"
      "  net_b b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// UDNT mixing rule applies to enable variants too.
TEST(BidirectionalSwitchUdnt, Tranif1RejectsUdntWithBuiltin) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a;\n"
      "  wire b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Control input acceptance: nets are 4-state by default and may serve as
// the control input of a pass-enable switch.
TEST(BidirectionalSwitchControlType, Tranif1AcceptsWireControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Control input acceptance: a 4-state variable (logic) is permitted.
TEST(BidirectionalSwitchControlType, Tranif1AcceptsLogicVariableControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  logic en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Control input acceptance: a 2-state variable (bit) is permitted.
TEST(BidirectionalSwitchControlType, Tranif0AcceptsBitVariableControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  bit en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Control input rejection: a real variable is not one of the three permitted
// control input types.
TEST(BidirectionalSwitchControlType, Tranif1RejectsRealControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  real en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Rtranif0RejectsStringControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  string en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Tranif0RejectsChandleControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  chandle en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Rtranif1RejectsEventControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  event en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
