#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(UnpackedArraySimulation, ElementWriteAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = arr[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAAu);
}

TEST(UnpackedArraySimulation, RangeFormElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[2] = 8'h42;\n"
      "    result = mem[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x42u);
}

// §7.4.2 / §11.2.1: the size of a fixed-size unpacked array may be given by a
// parameter. End-to-end, the top element is only addressable when that bound
// resolves in the parameter scope; a mis-resolved (zero) size would make this
// access fall outside the array.
TEST(UnpackedArraySimulation, ParameterSizedArrayElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int N = 4;\n"
      "  logic [7:0] arr [N];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[3] = 8'h55;\n"
      "    result = arr[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x55u);
}

// The three cases above declare at module scope, which the lowerer builds. A
// declaration written inside a procedural block is built by
// CreateBlockArrayElements in statement_assign_decl.cpp instead, and that read
// only §7.4.2's range form: the size form registered no array and created no
// elements, so `a[i]` was a bit-select of the single carrier variable the
// declaration left behind. Each case below is carried out through a
// module-scope scalar, because a block-local array's element variables go away
// with the block and cannot be looked up once the run has ended.

// §7.4.2: "[size] shall mean the same as [0:size-1]", so index 2 of `int a[3]`
// is the top element and holds what was written to it. A bit-select of the
// carrier writes bit 2 instead, and 9 truncated to that one bit reads 1.
TEST(UnpackedArraySimulation, SizeFormInAProceduralBlockAddressesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    a[0] = 7;\n"
      "    a[2] = 9;\n"
      "    result = a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §7.4.2 states the two spellings as the same array, giving `int Array[8][32]`
// and `int Array[0:7][0:31]` as one declaration written two ways, so the claim
// is an equality rather than two readings that happen to agree. The range form
// already built its array here, so the comparison reads 0 while the size form
// does not: 5 written through a bit-select comes back as 1.
TEST(UnpackedArraySimulation, SizeFormAndRangeFormAgreeInAProceduralBlock) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    int b[0:2];\n"
      "    a[2] = 5;\n"
      "    b[2] = 5;\n"
      "    result = (a[2] == b[2]);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// One element read cannot say the elements are separate storage: three bits of
// one carrier answer to three indices too. Writing all three and summing them
// separates the readings, 11 + 22 + 33 against the 1 + 0 + 1 that the low three
// bits of the carrier hold once each value has been cut down to one bit.
TEST(UnpackedArraySimulation, SizeFormInAProceduralBlockGivesEachIndexItsOwn) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    a[0] = 11;\n"
      "    a[1] = 22;\n"
      "    a[2] = 33;\n"
      "    result = a[0] + a[1] + a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 66u);
}

// §7.10 writes a queue's dimension as `$`, which is not a size however much it
// looks like one dimension written in one pair of brackets. CreateBlockQueue is
// asked before the array builder and answers for it; this case is what says the
// size form did not take the queue's dimension away from it, and it would read
// 0 from a queue that was never built.
TEST(UnpackedArraySimulation, QueueDimensionInAProceduralBlockIsNotASize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

// §7.4.2 in an instantiated module: `int a[4]` declared in M, which top
// instantiates as `m`, is stored under "m.a" and its elements under "m.a[i]",
// and §23.9 resolves the bare name `a` inside M through the instance. The
// lookup for the array's shape (SimContext::FindArrayInfo) asked for the bare
// key alone, so an element read `a[1]` found no array and fell to a bit-select
// of the carrier variable the lowerer creates under the name -- a carrier the
// element writes never touch -- reading 0 for both terms; the elements read
// back 22 and 44.
TEST(UnpackedArraySimulation, ChildInstanceElementsReadBackByBareName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int a[4];\n"
      "  int r;\n"
      "  initial begin\n"
      "    a[0] = 11;\n"
      "    a[1] = 22;\n"
      "    a[2] = 33;\n"
      "    a[3] = 44;\n"
      "    r = a[1] * 100 + a[3];\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 2244u);
}

// §12.7.3 and §20.7 on the same array: foreach steps through the four
// elements and $size answers the declared dimension, both asking the array's
// shape by its bare name inside the instance (§23.9). With no shape found,
// foreach ran once per bit of the 32-bit carrier and $size measured that
// carrier, answering 32; the loop fills 10, 20, 30, 40 and the sum is 100
// under a size of 4.
TEST(UnpackedArraySimulation, ChildInstanceForeachAndSizeSeeTheArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int a[4];\n"
      "  int r, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    foreach (a[i]) a[i] = (i + 1) * 10;\n"
      "    foreach (a[i]) s = s + a[i];\n"
      "    r = $size(a) * 1000 + s;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 4100u);
}

}  // namespace
