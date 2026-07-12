#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(MultidimensionalArraySimulation, PackedAndUnpackedDims) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'hDEADBEEF;\n"
      "    result = joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

TEST(MultidimensionalArraySimulation, DistinctUnpackedElementsAreIndependent) {
  // §7.4.4: each unpacked index selects a separate element. Writing two
  // different elements and combining them in one expression shows they hold
  // independent storage rather than aliasing.
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'h11111111;\n"
      "    joe[2] = 32'h22222222;\n"
      "    result = joe[2] - joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x11111111u);
}

TEST(MultidimensionalArraySimulation, PackedElementParticipatesInArithmetic) {
  // §7.4.4: an element of a multidimensional array is a single packed word
  // (here 32 bits from [3:0][7:0]) and takes part in arithmetic as one value,
  // mirroring the standard's whole-element add of one array slot into another.
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[8] = 32'h0000000F;\n"
      "    joe[9] = joe[8] + 1;\n"
      "    result = joe[9];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

TEST(MultidimensionalArraySimulation, PackedDimsViaTypedefStagingWidthHonored) {
  // §7.4.4: packed dimensions staged through a typedef combine into one wide
  // packed word. bsix is bit [1:5]; `bsix [1:10] v5` stacks a second packed
  // range on top, giving a single 50-bit value. Filling it with '1 and reading
  // it into a 64-bit register must yield 50 set bits, proving the staged
  // dimension sizes the storage rather than being dropped down to 5 bits.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:10] v5;\n"
      "  logic [63:0] result;\n"
      "  initial begin\n"
      "    v5 = '1;\n"
      "    result = v5;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x0003FFFFFFFFFFFFull);  // 50 ones
}

TEST(MultidimensionalArraySimulation,
     UnpackedDimsViaTypedefStagingAddressable) {
  // §7.4.4: unpacked dimensions may also be assembled in stages through a
  // typedef. mem_type is an array [0:3] of bsix; `mem_type ba [0:7]` prepends a
  // second unpacked range, so ba is addressed with two unpacked indices
  // [0:7][0:3]. Distinct two-index elements hold independent 5-bit words.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [1:5] bsix;\n"
      "  typedef bsix mem_type [0:3];\n"
      "  mem_type ba [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    ba[0][0] = 5'd7;\n"
      "    ba[7][3] = 5'd9;\n"
      "    ba[0][3] = 5'd1;\n"
      "    result = ba[0][0] + ba[7][3] + ba[0][3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 17u);
}

TEST(MultidimensionalArraySimulation,
     ThreeUnpackedDimsIndexIndependentElements) {
  // §7.4.4: a multidimensional array is an array of arrays. A three-dimensional
  // unpacked array A[2][3][4] is addressed by three indices; each fully indexed
  // element is independent storage, so writing three distinct slots and
  // combining them recovers exactly the written values.
  auto v = RunAndGet(
      "module t;\n"
      "  int A[2][3][4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    A[0][0][0] = 100;\n"
      "    A[1][2][3] = 20;\n"
      "    A[0][2][1] = 3;\n"
      "    result = A[0][0][0] + A[1][2][3] + A[0][2][1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

}  // namespace
