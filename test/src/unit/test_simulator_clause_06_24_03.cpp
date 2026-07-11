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

// §6.24.3: a queue is a dynamically sized array and thus a bit-stream type.
// When packed, the element at index 0 occupies the most significant bits, so a
// four-element byte queue casts to the same integer a fixed byte array would.
// The queue is built from real §7.10 push_back calls and driven through the
// full pipeline so the packing is observed on the live queue.
TEST(BitStreamCastSim, BitStreamQueueSourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q [$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'hDE);\n"
      "    q.push_back(8'hAD);\n"
      "    q.push_back(8'hBE);\n"
      "    q.push_back(8'hEF);\n"
      "    result = int'(q);\n"
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

// §6.24.3: the first conversion step packs the source into a generic value that
// is 4-state when the source carries any 4-state data. Exercise this through a
// queue source (the dynamically sized bit-stream form) so an X in the queue's
// leading element survives into the packed cast result.
TEST(BitStreamCastSim, BitStreamQueueSourceFourStatePropagates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'b1010_xxxx);\n"
      "    q.push_back(8'h55);\n"
      "    result = 16'(q);\n"
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

// §6.24.3: the second conversion step assigns the generic packed value to the
// destination, and where the destination designates a 2-state type the packed
// bits are assigned as if cast to 2-state. So casting a 4-state source array
// that carries X into a 2-state `int` destination yields a purely 2-state
// result: the unknown bits become 0 while the known bytes survive in place.
TEST(BitStreamCastSim, FourStateSourceIntoTwoStateDestStripsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
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
  ASSERT_GT(var->value.nwords, 0u);
  // The destination is 2-state, so no unknown bits survive.
  EXPECT_EQ(var->value.words[0].bval, 0u);
  // The fully known low byte (arr[1]) is preserved.
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x55u);
}

// §6.24.3: a dynamic array is a dynamically sized bit-stream type; when packed,
// the element at index 0 takes the most significant bits, just as for a queue
// or a fixed array. The dynamic array is built from real §7.5 syntax -- a
// new[] allocation followed by per-element writes -- and driven through the
// full pipeline so the packing is observed on the live dynamic array.
TEST(BitStreamCastSim, BitStreamDynamicArraySourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte d [];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[0] = 8'hDE;\n"
      "    d[1] = 8'hAD;\n"
      "    d[2] = 8'hBE;\n"
      "    d[3] = 8'hEF;\n"
      "    result = int'(d);\n"
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

// §6.24.3: bit-stream casting converts between aggregate types, including from
// a dynamically sized type into a structure. Casting a two-byte queue into a
// 16-bit packed struct reinterprets the packed bits, with the index-0 element
// landing in the most significant field. The queue is built from real §7.10
// push_back calls and the struct destination is observed after the run.
TEST(BitStreamCastSim, BitStreamQueueSourceToPackedStruct) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  byte q [$];\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    q.push_back(8'hCA);\n"
      "    q.push_back(8'hFE);\n"
      "    p = pair_t'(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// §6.24.3: an associative array is a legal bit-stream cast source (only its use
// as a destination is prohibited). When packed, its items are placed in
// index-sorted order with the first key's element in the most significant bits.
// The keys are written out of insertion order to show the ordering follows the
// sorted key sequence, not insertion order. Built from real §7.8 associative
// array syntax and driven through the full pipeline.
TEST(BitStreamCastSim, BitStreamAssocSourcePacksInIndexSortedOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte amap [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    amap[3] = 8'hEF;\n"
      "    amap[1] = 8'hAD;\n"
      "    amap[0] = 8'hDE;\n"
      "    amap[2] = 8'hBE;\n"
      "    result = int'(amap);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Sorted keys 0,1,2,3 -> DE (MSB), AD, BE, EF (LSB).
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

}  // namespace
