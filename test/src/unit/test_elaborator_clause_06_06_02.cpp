#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UwireElaboration, UwireNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire uw;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "uw");
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

TEST(UwireElaboration, UwireSingleContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireMultipleContinuousAssignmentsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireNetDeclAssignPlusContinuousAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, MultipleContinuousAssignmentsOnPlainWireOk) {
  // The single-driver restriction is specific to uwire: an ordinary wire
  // resolves multiple drivers, so two continuous assignments are not an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireOnBidirectionalSwitchTerminalError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireOnSecondBidirectionalTerminalError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  uwire b;\n"
      "  wire ctrl;\n"
      "  tranif1 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireBitSelectOnBidirectionalTerminalError) {
  // Connecting a single bit of a uwire net to a bidirectional terminal is
  // still connecting (a bit of) a uwire net, so it is an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire [1:0] u;\n"
      "  wire w;\n"
      "  tran sw(u[0], w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireOnResistiveBidirectionalSwitchTerminalError) {
  // The restriction applies to every bidirectional pass switch variant,
  // including the resistive rtran.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  rtran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireOnEnableLowControlSwitchTerminalError) {
  // The restriction applies to the enable-low control switch tranif0; a uwire
  // on either of its two bidirectional terminals is an error.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  wire ctrl;\n"
      "  tranif0 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireOnResistiveEnableLowControlSwitchTerminalError) {
  // rtranif0 is the resistive enable-low control bidirectional pass switch;
  // the second bidirectional terminal here carries the uwire.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  uwire b;\n"
      "  wire ctrl;\n"
      "  rtranif0 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireOnResistiveEnableHighControlSwitchTerminalError) {
  // rtranif1 is the resistive enable-high control bidirectional pass switch.
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire a;\n"
      "  wire b;\n"
      "  wire ctrl;\n"
      "  rtranif1 sw(a, b, ctrl);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, PlainWireOnBidirectionalSwitchTerminalOk) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  wire b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire [3:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 4u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

}  // namespace
