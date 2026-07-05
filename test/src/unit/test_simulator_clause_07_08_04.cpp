#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.8.4 governs the runtime behavior of an associative array whose index is an
// integral data type: the index expression is cast to the declared index type,
// a 4-state index carrying x/z is invalid, and the iteration order follows the
// signedness of the index type. Every test below builds the array (and, where
// it matters, the index expression) from real source so the declared width and
// signedness are produced by the elaborator and consumed by the run-time cast,
// rather than hand-stamped onto an AssocArraySpec. Dependency §7.8.1 supplies
// the associative-array declaration syntax; §6.24.1 the cast machinery.

// Basic write-then-read through the full pipeline: an integral-index array
// stores a value under a key and reads it back at that same key.
TEST(IntegralIndexAssocArraySimulation, WriteAndReadEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[5] = 42;\n"
                      "    result = aa[5];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §7.8.4: the index expression is cast to the index type, then entries are
// ordered by signed numerical value when the index type is signed. A signed
// 4-bit index sign-extends 12 (0b1100) to -4, so it orders ahead of the key 3.
// The same source keys ordered the opposite way under an unsigned index type
// (next test), isolating the signedness of the ordering rule.
TEST(IntegralIndexAssocArraySimulation, SignedIndexCastAndOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  int aa[SNibble];\n"
      "  initial begin\n"
      "    aa[3] = 100;\n"
      "    aa[12] = 200;\n"  // sign-extends to key -4
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 2u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, -4);  // 12 cast to signed 4-bit
  EXPECT_EQ(it->second.ToUint64(), 200u);
  ++it;
  EXPECT_EQ(it->first, 3);
  EXPECT_EQ(it->second.ToUint64(), 100u);
}

// §7.8.4: an unsigned index type zero-extends the cast and orders unsigned, so
// the very same source keys (3 and 12) come out as 3 then 12 rather than -4
// then 3 as under the signed index type above.
TEST(IntegralIndexAssocArraySimulation, UnsignedIndexCastAndOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int aa[UNibble];\n"
      "  initial begin\n"
      "    aa[3] = 100;\n"
      "    aa[12] = 200;\n"  // zero-extends to key 12
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 2u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, 3);
  EXPECT_EQ(it->second.ToUint64(), 100u);
  ++it;
  EXPECT_EQ(it->first, 12);  // 12 cast to unsigned 4-bit stays 12
  EXPECT_EQ(it->second.ToUint64(), 200u);
}

// §7.8.4: a signed 8-bit index type sign-extends the cast, so the source key
// 200 (0xC8, top bit set) becomes the negative key -56 and no entry lands at
// 200. This mirrors the LRM's signed-nibble example at byte width.
TEST(IntegralIndexAssocArraySimulation, SignedByteSignExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit signed [7:0] SByte;\n"
      "  int aa[SByte];\n"
      "  initial aa[200] = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->int_data.count(-56), 1u);
  EXPECT_EQ(aa->int_data.count(200), 0u);
}

// §7.8.4: an unsigned 8-bit index type zero-extends, so the source key 200
// stays 200 and does not alias the sign-extended value -56.
TEST(IntegralIndexAssocArraySimulation, UnsignedByteZeroExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [7:0] UByte;\n"
      "  int aa[UByte];\n"
      "  initial aa[200] = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->int_data.count(200), 1u);
  EXPECT_EQ(aa->int_data.count(-56), 0u);
}

// §7.8.4: casting to the index type narrows a value wider than the index width.
// With a 4-bit unsigned index, 19 (0x13) collapses onto the same key as 3
// (0x13 & 0xF == 0x3), so the second write overwrites the first entry.
TEST(IntegralIndexAssocArraySimulation, IndexTruncatedToWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int aa[UNibble];\n"
      "  initial begin\n"
      "    aa[3] = 1;\n"
      "    aa[19] = 2;\n"  // 19 & 0xF == 3, collapses onto key 3
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_EQ(aa->Size(), 1u);
  ASSERT_EQ(aa->int_data.count(3), 1u);
  EXPECT_EQ(aa->int_data.at(3).ToUint64(), 2u);
}

// §7.8.4: the cast applies identically on reads and writes, so a value stored
// under an unsigned 8-bit key of 200 is found again by reading 200. If the read
// path sign-extended instead, it would look up -56 and miss.
TEST(IntegralIndexAssocArraySimulation, UnsignedCastReadRoundtrip) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef bit [7:0] UByte;\n"
                      "  int aa[UByte];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[200] = 99;\n"
                      "    result = aa[200];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §7.8.4: a signed index orders and keys by signed value, so a negative key is
// a first-class entry that reads back at the same negative index.
TEST(IntegralIndexAssocArraySimulation, SignedNegativeKeyRoundtrip) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    aa[-3] = 77;\n"
                      "    result = aa[-3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            77u);
}

// §7.8.4: a 4-state index expression containing x or z is invalid, so a write
// through it stores nothing and raises a diagnostic. The x/z is detected on the
// evaluated index value before the cast, independent of the index type.
TEST(IntegralIndexAssocArraySimulation, XZIndexInvalidWrite) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  initial aa[8'bxx] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_TRUE(aa->int_data.empty());
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §7.8.4: the x/z-invalid rule applies to reads as well, so reading through an
// x/z index misses (returning the array default) and raises a diagnostic; the
// valid entry stored on the same array is untouched.
TEST(IntegralIndexAssocArraySimulation, XZIndexInvalidRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[8'bxx];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0u);  // array default for a miss
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §7.8.4 + §6.24.1 end-to-end: an explicit real→int cast produces an integral
// index built entirely from real cast syntax. int'(3.0) evaluates to key 3, so
// the value stored through the cast is read back at 3. This drives the cast
// dependency through the full pipeline rather than pre-computing the key.
TEST(IntegralIndexAssocArraySimulation, ExplicitRealCastIndexEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int aa[int];\n"
                      "  real r;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    r = 3.0;\n"
                      "    aa[int'(r)] = 55;\n"
                      "    result = aa[3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

// §7.8.4: for the builtin signed `int` index type (the LRM example's first
// form), entries iterate in signed numerical order, so a negative key sorts
// ahead of the positive ones. Keys are inserted out of order from real source.
TEST(IntegralIndexAssocArraySimulation, SignedBuiltinIntOrdering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  initial begin\n"
      "    aa[10] = 1;\n"
      "    aa[-5] = 2;\n"
      "    aa[3] = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  ASSERT_EQ(aa->int_data.size(), 3u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, -5);
  ++it;
  EXPECT_EQ(it->first, 3);
  ++it;
  EXPECT_EQ(it->first, 10);
}

// §7.8.4: the x/z-invalid rule bites when the x/z arrives through a 4-state
// index variable (only a 4-state type such as `integer` can hold x/z), not just
// a literal. Using the LRM example's `integer` index type, an x-valued index
// stores nothing and raises a diagnostic.
TEST(IntegralIndexAssocArraySimulation, IntegerVariableXZIndexInvalid) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  initial begin\n"
      "    idx = 2'bxx;\n"
      "    aa[idx] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_NE(aa, nullptr);
  EXPECT_TRUE(aa->int_data.empty());
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

}  // namespace
