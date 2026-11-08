#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(AssignEvalSteps, NoExtensionWhenWidthsMatch) {
  SimFixture f;
  auto val = MakeLogic4VecVal(f.arena, 8, 0xFF);
  val.is_signed = true;
  auto result = ResizeToWidth(val, 8, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(AssignEvalSteps, SignedSourceWidensWithSignExtensionEndToEnd) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] b;\n"
      "  logic signed [15:0] a;\n"
      "  initial begin\n"
      "    b = -1;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0xFFFFu);
}

TEST(AssignEvalSteps, UnsignedSourceWidensWithZeroExtensionEndToEnd) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0x00FFu);
}

TEST(AssignEvalSteps, SignedPositiveSourceZeroFillsAboveSignBitEndToEnd) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] b;\n"
      "  logic signed [15:0] a;\n"
      "  initial begin\n"
      "    b = 8'h7F;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0x007Fu);
}

TEST(AssignEvalSteps, SignedSourceSignExtendsThroughNonblockingAssignment) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] b;\n"
      "  logic signed [15:0] a;\n"
      "  initial begin\n"
      "    b = -1;\n"
      "    a <= b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0xFFFFu);
}

TEST(AssignEvalSteps, SignedSourceSignExtendsThroughContinuousAssignment) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] b;\n"
      "  logic signed [15:0] a;\n"
      "  assign a = b;\n"
      "  initial b = -1;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0xFFFFu);
}

TEST(AssignEvalSteps, UnsignedSourceZeroExtendsThroughContinuousAssignment) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  logic [15:0] a;\n"
      "  assign a = b;\n"
      "  initial b = 8'hFF;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0x00FFu);
}

TEST(AssignEvalSteps, SignedWideRhsSignExtendsAcrossWords) {
  SimFixture f;
  auto val = MakeLogic4Vec(f.arena, 70);
  val.words[1].aval = uint64_t{1} << 5;
  val.is_signed = true;
  auto result = ResizeToWidth(val, 130, f.arena);
  EXPECT_EQ(result.width, 130u);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[1].aval, ~uint64_t{0} << 5);
  EXPECT_EQ(result.words[2].aval, 0x3u);
}

TEST(AssignEvalSteps, UnsignedWideRhsZeroExtendsAcrossWords) {
  SimFixture f;
  auto val = MakeLogic4Vec(f.arena, 70);
  val.words[1].aval = uint64_t{1} << 5;
  val.is_signed = false;
  auto result = ResizeToWidth(val, 130, f.arena);
  EXPECT_EQ(result.width, 130u);
  EXPECT_EQ(result.words[1].aval, uint64_t{1} << 5);
  EXPECT_EQ(result.words[2].aval, 0u);
}

}  // namespace
