#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BitStreamCastSim, BitStreamArrayToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hDE;\n"
      "    arr[1] = 8'hAD;\n"
      "    arr[2] = 8'hBE;\n"
      "    arr[3] = 8'hEF;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, BitStreamShortArrayToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 16'hCAFE;\n"
      "    arr[1] = 16'hBABE;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEu);
}

TEST(BitStreamCastSim, BitStreamStructRoundTrip) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  int flat;\n"
      "  pair_t p2;\n"
      "  initial begin\n"
      "    p = 16'hCAFE;\n"
      "    flat = int'(p);\n"
      "    p2 = pair_t'(flat);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* p2 = f.ctx.FindVariable("p2");
  ASSERT_NE(p2, nullptr);
  EXPECT_EQ(p2->value.ToUint64(), 0xCAFEu);
}

TEST(BitStreamCastSim, SingleElementArrayCast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte arr [1];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAB;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(BitStreamCastSim, PackedStructToIntPreservesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  int flat;\n"
      "  initial begin\n"
      "    p = 16'hCAFE;\n"
      "    flat = int'(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("flat");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// §6.24.3: when the source carries any 4-state bit, the packed bit-stream is
// itself 4-state. Pre-seed the array's high element with an X-bearing logic
// value so that the cast result preserves an unknown bit in the expected
// position.
TEST(BitStreamCastSim, BitStreamSourceFourStatePropagates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [2];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
      "    result = 16'(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

}  // namespace
