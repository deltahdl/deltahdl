#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PlaArrayType, OutputsUpdatedWithoutDelay) {
  SimFixture f;
  uint64_t cap = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  logic [1:1] cap;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    cap = out;\n"
                           "  end\n"
                           "endmodule\n",
                           "cap");
  EXPECT_EQ(cap, 1u);
}

TEST(PlaArrayType, AsyncReevaluatesOnInputChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
}

TEST(PlaArrayType, SyncDoesNotReevaluateOnInputChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

TEST(PlaArrayType, SyncReevaluatesWhenCalledAgain) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
}

TEST(PlaArrayType, AsyncReevaluatesOnMemoryChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    #1 mem[1] = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

TEST(PlaArrayType, AsyncOutputUpdatedWithoutDelay) {
  SimFixture f;
  uint64_t cap = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  logic [1:1] cap;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    in = 2'b10;\n"
                           "    cap = out;\n"
                           "  end\n"
                           "endmodule\n",
                           "cap");
  EXPECT_EQ(cap, 0u);
}

TEST(PlaArrayType, AsyncDrivesConcatenatedTermsOnInputChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a1, a2;\n"
      "  logic b1, b2;\n"
      "  logic [1:2] mem [1:2];\n"
      "  initial begin\n"
      "    a1 = 1'b1;\n"
      "    a2 = 1'b1;\n"
      "    mem[1] = 2'b10;\n"
      "    mem[2] = 2'b01;\n"
      "    $async$and$array(mem, {a1, a2}, {b1, b2});\n"
      "    #1 a2 = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 1u);
  EXPECT_EQ(b2->value.ToUint64(), 0u);
}

TEST(PlaArrayType, SyncDrivesConcatenatedOutputTerms) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a1, a2;\n"
      "  logic b1, b2;\n"
      "  logic [1:2] mem [1:2];\n"
      "  initial begin\n"
      "    a1 = 1'b1;\n"
      "    a2 = 1'b0;\n"
      "    mem[1] = 2'b10;\n"
      "    mem[2] = 2'b01;\n"
      "    $sync$and$array(mem, {a1, a2}, {b1, b2});\n"
      "    #1 a1 = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 1u);
  EXPECT_EQ(b2->value.ToUint64(), 0u);
}

}  // namespace
