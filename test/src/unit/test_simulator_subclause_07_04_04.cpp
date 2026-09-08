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

TEST(MultidimensionalArraySimulation, NonblockingReachesSameElementAsBlocking) {
  // §10.4.2: the variable_lvalue of a nonblocking assignment is "a data type
  // that is valid for a procedural assignment statement", and §7.4.5 makes an
  // indexed name one such lvalue, so `A[1][2] <= 9` must land in the very
  // element `A[1][2] = 9` would have written. The two elements are read out of
  // the run by their own names rather than summed, because a sum cannot say
  // which of them carried the value -- nor that the array's base variable took
  // it instead. The delay lets the update region run: a nonblocking assignment
  // read back at time 0 still shows the old value. 9 is odd on purpose; an
  // even value would leave a wrongly written base variable at 0 as well.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[0][0] = 7;\n"
      "    A[1][2] <= 9;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* written_blocking = f.ctx.FindVariable("A[0][0]");
  auto* written_nonblocking = f.ctx.FindVariable("A[1][2]");
  ASSERT_NE(written_blocking, nullptr);
  ASSERT_NE(written_nonblocking, nullptr);
  EXPECT_EQ(written_blocking->value.ToUint64(), 7u);
  EXPECT_EQ(written_nonblocking->value.ToUint64(), 9u);
}

// §7.4.4 makes a multidimensional array an array of arrays, so the name of one
// of its inner arrays is itself an aggregate and `mirror[0][0] = bank[0][0]`
// copies the two elements that inner array holds. §6.8 gives each of those
// four names its own storage -- "A variable is an abstraction of a data storage
// element. A variable shall store a value from one assignment to the next" --
// which TrySubarrayAssign (src/simulator/statement_assign_core.cpp) has to
// leave standing. It gathers the source subarray by walking the context for the
// leaves under that prefix and stores each leaf's Logic4Vec into the matching
// destination leaf, and a Logic4Vec copies its `words` pointer rather than the
// words (src/common/types.h), so the two subarrays were one row of storage read
// under two names.
//
// This handler neither resizes nor coerces, so the copy is silent where it is
// made and the case writes one destination leaf afterwards and reads the source
// leaf it was paired with. It is a regression guard rather than a
// discriminator: no writer left in the tree reaches an unpacked-array leaf's
// words in place. WriteVar puts its own resized value in the leaf before it
// applies §6.11.2, WritePartSelect deposits into a fresh extract of the target,
// §13.5.1's argument binding owns its copy since #3564, and a member deposit
// cannot resolve against an indexed name at all, BuildLhsName
// (src/simulator/statement_assign.cpp) having no select arm. A 2-state
// destination is what would make it bite -- the leaves of a multidimensional
// array do carry their declared state-ness, unlike those of a one-dimensional
// one -- because this store leaves the source's words in the destination and
// coercing them there would clear the source.
//
// Three dimensions because two do not reach this handler: TrySubarrayAssign
// asks for a select of a select on both sides, and on `bank[2][2]` the name
// `bank[0]` is a select of a plain identifier.
//
// ToUint64 would report nothing here. It projects aval & ~bval, so an unknown
// bit already reads as 0 through it; the assertions read words[0] instead.
// 8'b0x11z000 is stored as aval 0x70 with bval 0x48, an x digit being aval 1
// with bval 1 and a z digit aval 0 with bval 1, and the 2-state conversion of
// it would be aval 0x30 with bval 0x00. The second leaf is what says the
// subarray copy ran at all.
TEST(MultidimensionalArraySimulation, SubarrayCopyElementsGetTheirOwnWords) {
  SimFixture f;
  auto* origin = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] bank [2][2][2];\n"
      "  logic [7:0] mirror [2][2][2];\n"
      "  initial begin\n"
      "    bank[0][0][0] = 8'b0x11z000;\n"
      "    bank[0][0][1] = 8'h3C;\n"
      "    mirror[0][0] = bank[0][0];\n"
      "    mirror[0][0][0] = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f, "bank[0][0][0]");
  ASSERT_NE(origin, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* overwritten = f.ctx.FindVariable("mirror[0][0][0]");
  auto* carried = f.ctx.FindVariable("mirror[0][0][1]");
  ASSERT_NE(overwritten, nullptr);
  ASSERT_NE(carried, nullptr);
  EXPECT_EQ(origin->value.words[0].aval & 0xFFu, 0x70u);
  EXPECT_EQ(origin->value.words[0].bval & 0xFFu, 0x48u);
  EXPECT_EQ(overwritten->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(carried->value.words[0].aval & 0xFFu, 0x3Cu);
}

// §7.4.4: "A multidimensional array is an array of arrays", so `int
// a[0:1][0:2]` is two arrays of three, six elements in all. A declaration
// inside a begin-end block was built from its first dimension alone, so the
// array had two elements and a write to `a[1][2]` reached a leaf nothing had
// created. The read is what says so: the write was silent either way.
TEST(MultidimensionalArraySimulation, BlockLocalArrayBuildsEveryDimension) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[0:1][0:2];\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

// §7.4.2's size form of the same declaration -- the clause gives
// `int Array[8][32]` and `int Array[0:7][0:31]` as the same array -- which the
// block builder read only for a lone dimension while the range form beside it
// took the first of several.
TEST(MultidimensionalArraySimulation, BlockLocalArrayBuildsEverySizeFormDim) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[2][3];\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

// The per-dimension extents rather than the leaves: a foreach reads dim_sizes,
// which the block path left empty, so it iterated the outermost dimension alone
// and this counted 2 where §7.4.4 gives 6.
TEST(MultidimensionalArraySimulation,
     BlockLocalArrayRecordsEveryDimensionSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[0:1][0:2];\n"
      "    result = 0;\n"
      "    foreach (a[i, j]) result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

// The same declaration among a module's items, which says the two builders
// agree rather than that one of them works.
TEST(MultidimensionalArraySimulation, ModuleScopeArrayAgreesWithTheBlockLocal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[0:1][0:2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

// §7.4.5: "Writing to an array with an invalid index shall perform no
// operation, with the exceptions of writing to element [$+1] of a queue ... and
// creating a new element of an associative array". A fixed unpacked array is
// neither exception, and the write invented a variable for the name it built
// instead -- 32 bits wide whatever the element type declared, in the
// design-wide table under a name FindVariable will not read back from inside an
// instance, and made again on every execution. Nothing existing under the name
// afterwards is what says the operation was not performed.
TEST(MultidimensionalArraySimulation,
     WriteToAnAbsentCompoundElementIsNoOperation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 5;\n"
      "    a[i][0] = 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a[5][0]"), nullptr);
}

// The same write executed twice: the fabrication made one cell per execution,
// so a loop writing an out-of-range element grew the table for as long as it
// ran.
TEST(MultidimensionalArraySimulation, RepeatedAbsentCompoundWriteMakesNoCells) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 5; i < 7; i = i + 1)\n"
      "      a[i][0] = 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a[5][0]"), nullptr);
  EXPECT_EQ(f.ctx.FindVariable("a[6][0]"), nullptr);
}

// The guard: an index that is in range names an element that exists, and the
// write reaches it at the element's own declared width rather than the 32 the
// fabricated cell had.
TEST(MultidimensionalArraySimulation, WriteToAPresentCompoundElementReachesIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    a[i][2] = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f, "a[1][2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
