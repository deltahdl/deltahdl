#include "fixture_elaborator.h"
#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(ClockingBlockElab, UnnamedNonDefaultBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, UnnamedDefaultBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToInputClockvarError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, InoutClockvarReadOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.bidir;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, InoutClockvarWriteOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.bidir = 8'hFF;\n"
             "  end\n"
             "endmodule\n"));
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

}  // namespace
