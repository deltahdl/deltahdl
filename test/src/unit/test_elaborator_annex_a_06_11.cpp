#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// --- ClockingBlockElab: clocking_declaration elaboration ---

TEST(ClockingBlockElab, PlainBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, MultipleDirectionGroups) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "    inout c;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, DefaultSkewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, MultipleBlocksElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb1 @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cb2 @(posedge clk2);\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, AssertionItemDeclElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingBlockElab, EdgeKeywordInSkewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input edge data;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- ClockingSkewElab: clocking_skew elaboration ---

TEST(ClockingSkewElab, SkewVariationsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step data;\n"
      "    output negedge #1 ack;\n"
      "    input posedge ready;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockingSkewElab, ExplicitZeroInputSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #0 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, ExplicitZeroOutputSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #0 ack;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, ParameterAsSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter SKEW = 3;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #SKEW data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewElab, InputOutputCombinedSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #5 output #6 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// --- CycleDelayElab: cycle_delay elaboration ---

TEST(CycleDelayElab, WithDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(CycleDelayElab, ParenthesizedExprWithDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##(3 + 2);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(CycleDelayElab, ZeroCycleDelayWithDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##0;\n"
             "  end\n"
             "endmodule\n"));
}

// --- DefaultClockingElab: default clocking elaboration ---

TEST(DefaultClockingElab, InlineDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, UnnamedDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, ReferenceFormElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  default clocking cb;\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, DefaultClockingInInterfaceElaborates) {
  EXPECT_TRUE(
      ElabOk("interface my_if (input clk);\n"
             "  logic [7:0] data;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endinterface\n"));
}

// --- GlobalClockingElab: global clocking elaboration ---

TEST(GlobalClockingElab, BasicGlobalClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking gclk @(posedge sys_clk);\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, UnnamedGlobalClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking @(posedge clk); endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, CompoundEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking sys @(clk1 or clk2); endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, GlobalClockingInInterfaceElaborates) {
  EXPECT_TRUE(
      ElabOk("interface my_if (input clk);\n"
             "  global clocking gc @(posedge clk); endclocking\n"
             "endinterface\n"));
}

TEST(GlobalClockingElab, GlobalAndDefaultCoexist) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking gc @(posedge clk); endclocking\n"
             "  default clocking dc @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// --- SyncDriveElab: clocking_drive elaboration ---

TEST(SyncDriveElab, SimpleClockingDriveElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= 8'hFF;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, DriveWithCycleDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= ##2 8'hFF;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, InoutClockvarDriveElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial cb.data <= 8'hAB;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, MultipleDrivesToSameOutputElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    output nibble;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.nibble <= 4'b0101;\n"
             "    cb.nibble <= 4'b0011;\n"
             "  end\n"
             "endmodule\n"));
}

// --- Additional coverage ---

TEST(ClockingBlockElab, ClockingBlockInProgramElaborates) {
  EXPECT_TRUE(
      ElabOk("program test(input logic clk);\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endprogram\n"));
}

TEST(ClockingBlockElab, SequenceDeclInBlockElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "    sequence s;\n"
             "      data;\n"
             "    endsequence\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(DefaultClockingElab, DefaultClockingInProgramElaborates) {
  EXPECT_TRUE(
      ElabOk("program test(input logic clk);\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endprogram\n"));
}

TEST(GlobalClockingElab, GlobalClockingInProgramElaborates) {
  EXPECT_TRUE(
      ElabOk("program test(input logic clk);\n"
             "  global clocking gc @(posedge clk); endclocking\n"
             "endprogram\n"));
}

TEST(CycleDelayElab, CycleDelayIdentifierWithDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##n;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
