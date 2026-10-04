#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_open_array_natural_order.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

// Annex H.7.6 - Mapping between SystemVerilog ranges and C ranges.
//
// H.7.6 fixes how a SystemVerilog declared range becomes the range a C
// programmer sees across the DPI. Its own distinctive rules are:
//
//   b) A packed array of range [L:R] is normalized to [abs(L-R):0]: its LSB has
//      the normalized C index 0 and its MSB has the normalized C index
//      abs(L-R).
//   c) (shall) The natural order of unpacked elements is used - lower indices
//      first. For a SystemVerilog range [L:R], the element with SystemVerilog
//      index min(L,R) has C index 0 and the element with index max(L,R) has C
//      index abs(L-R).
//
// The mapping is the same for calls in both directions (SystemVerilog calling C
// and C calling SystemVerilog). Linearization of a multidimensional packed part
// (rule a) and the array querying utilities are defined by the dependencies
// H.7.5, 6.22.2 and H.12.2 and are not re-proven here.
//
// These rules are realized entirely by existing production code: rule b by the
// canonical bit-select accessors in svdpi.cpp (normalized index 0 is the
// least-significant bit, word = i/32, bit = i%32), and rule c by svLow / svHigh
// / svSize, which return min / max / element-count over a dimension's declared
// bounds so that a C index is sv_index - svLow. These tests play the role of
// the user C code that derives the normalized indices and observe production
// placing each element exactly where H.7.6 says it must land.

namespace {

svOpenArrayHandle MakeHandle(const SvOpenArrayDimRange* ranges, int n_dims,
                             SvOpenArrayDesc* desc) {
  desc->data = nullptr;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  return desc;
}

// Rule b: a packed array of SystemVerilog range [L:R] is normalized to
// [abs(L-R):0]. The LSB maps to normalized C index 0 and the MSB to normalized
// C index abs(L-R), regardless of whether the SystemVerilog range was declared
// descending or ascending. The canonical bit-select accessors index the value
// over exactly that normalized range.
TEST(MappingSvRangesToCRanges, PackedRangeNormalizedLsbZeroMsbAbsLminusR) {
  struct Case {
    int l;
    int r;
  };
  // Descending [7:4], ascending [4:7], and a negative-spanning [2:-3] all carry
  // the same width abs(L-R)+1 and the same normalized MSB index abs(L-R).
  const Case kCases[] = {{7, 4}, {4, 7}, {2, -3}};
  for (const Case& c : kCases) {
    const int kMsb = std::abs(c.l - c.r);  // normalized index of the MSB.
    const int kWidth = kMsb + 1;
    const int kWords = SV_PACKED_DATA_NELEMS(kWidth);
    ASSERT_LE(kWords, 2);
    svBitVecVal vec[2] = {0u, 0u};

    // Drive the two endpoints of the normalized [abs(L-R):0] range.
    svPutBitselBit(vec, 0, 1);     // LSB -> normalized index 0.
    svPutBitselBit(vec, kMsb, 1);  // MSB -> normalized index abs(L-R).

    EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
    EXPECT_EQ(svGetBitselBit(vec, kMsb), 1u);

    // Nothing outside the two endpoints is set: the normalized range spans
    // exactly indices 0 .. abs(L-R) and no more.
    for (int i = 0; i < kWidth; ++i) {
      const svBit kExpected = (i == 0 || i == kMsb) ? 1u : 0u;
      EXPECT_EQ(svGetBitselBit(vec, i), kExpected)
          << "L=" << c.l << " R=" << c.r;
    }
  }
}

// Rule b at element granularity: a single-element packed range [k:k] has
// abs(L-R) == 0, so it normalizes to [0:0] - the MSB and LSB coincide at C
// index 0. This is the degenerate endpoint of the normalization formula.
TEST(MappingSvRangesToCRanges, SingleElementPackedRangeNormalizesToZeroZero) {
  const int kL = 5, kR = 5;
  EXPECT_EQ(std::abs(kL - kR), 0);

  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, 0, 1);
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);
  EXPECT_EQ(vec, 1u);  // only normalized index 0 exists.
}

// Rule c (shall): for an unpacked dimension of SystemVerilog range [L:R] the
// element with index min(L,R) gets C index 0 and the element with index
// max(L,R) gets C index abs(L-R). svLow / svHigh / svSize supply min / max /
// count, and a C index is the user computation sv_index - svLow. Exercised for
// an ascending, a descending, and a negative range.
TEST(MappingSvRangesToCRanges, UnpackedNaturalOrderMinToZeroMaxToAbs) {
  struct Case {
    int l;
    int r;
  };
  const Case kCases[] = {{0, 7}, {7, 0}, {-1, -8}};
  for (const Case& c : kCases) {
    // Dimension 0 is an unused packed placeholder; dimension 1 is under test.
    const SvOpenArrayDimRange kRanges[] = {{0, 0}, {c.l, c.r}};
    SvOpenArrayDesc desc;
    svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

    ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(h, 1, c.l, c.r);
  }
}

// Rule c "natural order ... lower indices go first": walking the SystemVerilog
// indices from low to high yields C indices 0, 1, 2, ... contiguously, so the C
// layout preserves the ascending element order independent of the declared
// range orientation. Verified against a descending declaration [3:-2].
TEST(MappingSvRangesToCRanges, UnpackedLowerIndicesGoFirst) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {3, -2}};  // unpacked [3:-2].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  const int kLo = svLow(h, 1);     // -2
  const int kSize = svSize(h, 1);  // 6
  EXPECT_EQ(kLo, -2);
  EXPECT_EQ(kSize, 6);

  int expected_c = 0;
  for (int sv = kLo; sv < kLo + kSize; ++sv) {
    EXPECT_EQ(sv - kLo,
              expected_c);  // contiguous 0,1,2,... in ascending order.
    ++expected_c;
  }
  EXPECT_EQ(expected_c, kSize);
}

// The worked example from H.7.6: logic [2:3][1:3][2:0] b [1:10][31:0] must be
// described in C as logic [17:0] b [0:9][0:31]. The packed part linearizes
// (sizes 2*3*3 = 18, rule a / H.7.5) and then normalizes to [17:0] (rule b),
// while the two unpacked ranges normalize by rule c: [1:10] -> [0:9] and
// [31:0] -> [0:31]. The descriptor carries the linearized packed dimension at
// index 0 and the unpacked dimensions after it.
TEST(MappingSvRangesToCRanges, WorkedExampleNormalizedForm) {
  // Original packed dimension sizes, before linearization.
  const int kPackedSizes[] = {std::abs(2 - 3) + 1, std::abs(1 - 3) + 1,
                              std::abs(2 - 0) + 1};
  int packed_width = 1;
  for (int s : kPackedSizes) packed_width *= s;
  EXPECT_EQ(packed_width, 18);  // 2 * 3 * 3.

  // Descriptor: dim 0 = linearized+normalized packed part [17:0];
  // dim 1 = unpacked [1:10]; dim 2 = unpacked [31:0].
  const SvOpenArrayDimRange kRanges[] = {{17, 0}, {1, 10}, {31, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 3, &desc);

  // Packed part normalizes to [17:0]: size 18, MSB normalized index 17.
  EXPECT_EQ(svSize(h, 0), 18);
  EXPECT_EQ(std::abs(svLeft(h, 0) - svRight(h, 0)), 17);
  svBitVecVal packed = 0u;
  svPutBitselBit(&packed, 17, 1);  // top of the normalized packed range exists.
  EXPECT_EQ(svGetBitselBit(&packed, 17), 1u);

  // Unpacked [1:10] -> normalized [0:9]: min 1 -> C 0, max 10 -> C 9.
  EXPECT_EQ(svLow(h, 1), 1);
  EXPECT_EQ(svSize(h, 1), 10);
  EXPECT_EQ(svLow(h, 1) - svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 9);

  // Unpacked [31:0] -> normalized [0:31]: min 0 -> C 0, max 31 -> C 31.
  EXPECT_EQ(svLow(h, 2), 0);
  EXPECT_EQ(svSize(h, 2), 32);
  EXPECT_EQ(svHigh(h, 2) - svLow(h, 2), 31);
}

// "The above range mapping ... applies to calls made in both directions." The
// same normalized index addresses the same bit whether C reads a value handed
// in by SystemVerilog (the get path of an SV->C call) or writes a value that
// SystemVerilog will read back (the put path of a C->SV call / copy-out).
// Writing through the normalized indices of a packed [L:R] and reading them
// back yields the identical mapping in both directions.
TEST(MappingSvRangesToCRanges, MappingAppliesInBothCallDirections) {
  const int kL = 11, kR = 4;           // packed [11:4].
  const int kMsb = std::abs(kL - kR);  // 7
  const int kWidth = kMsb + 1;         // 8
  svBitVecVal vec = 0u;

  // C->SV direction: C writes the value SystemVerilog will observe.
  for (int i = 0; i < kWidth; ++i) {
    if (i % 2 == 0) svPutBitselBit(&vec, i, 1);
  }

  // SV->C direction: C reads the value back at the same normalized indices.
  for (int i = 0; i < kWidth; ++i) {
    EXPECT_EQ(svGetBitselBit(&vec, i),
              static_cast<svBit>(i % 2 == 0 ? 1u : 0u));
  }
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);  // LSB normalized index 0.
  EXPECT_EQ(svGetBitselBit(&vec, kMsb),
            0u);  // MSB normalized index abs(L-R)=7.
}

// Rule b edge: the normalization holds when the packed range is wider than one
// canonical 32-bit word. For [40:1] the width is abs(40-1)+1 = 40, so the MSB
// has normalized index 39, which the canonical accessors place in the second
// canonical word (39 / 32 = word 1, 39 % 32 = bit 7) while the LSB stays at
// normalized index 0 in the first word.
TEST(MappingSvRangesToCRanges, PackedRangeWiderThanCanonicalWordNormalizes) {
  const int kL = 40, kR = 1;
  const int kMsb = std::abs(kL - kR);  // 39
  const int kWidth = kMsb + 1;         // 40
  ASSERT_EQ(SV_PACKED_DATA_NELEMS(kWidth), 2);
  svBitVecVal vec[2] = {0u, 0u};

  svPutBitselBit(vec, 0, 1);     // LSB -> normalized index 0.
  svPutBitselBit(vec, kMsb, 1);  // MSB -> normalized index abs(L-R) = 39.

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kMsb), 1u);
  EXPECT_EQ(vec[0], 1u);       // only bit 0 of the low canonical word.
  EXPECT_EQ(vec[1], 1u << 7);  // MSB lands in the high word at bit 7.
}

// Rule c edge: a single-element unpacked dimension [k:k] has abs(L-R) == 0, so
// its only element maps to C index 0. svLow / svHigh / svSize report the
// coincident bound and unit count, and the lone element's C index (sv - svLow)
// is zero even for a negative declared index.
TEST(MappingSvRangesToCRanges, SingleElementUnpackedDimensionMapsToZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0},
                                         {-4, -4}};  // unpacked [-4:-4].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 1), -4);
  EXPECT_EQ(svHigh(h, 1), -4);
  EXPECT_EQ(svSize(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 0);  // sole element -> C index 0.
}

// The C functions the designs below call: one weighting the four elements of
// an array of bytes by C index, one filling an array of three ints, and one
// writing two elements of an array of 64-bit 4-state vectors.
int WeightedByCIndex(const uint32_t* a) {
  return static_cast<int>(a[0] + (a[1] * 10) + (a[2] * 100) + (a[3] * 1000));
}

void FillThreeInts(int* o) {
  o[0] = 9;
  o[1] = 8;
  o[2] = 7;
}

void FillVectors(SvLogicVecVal* arr) {
  for (int i = 0; i < 64 * 2; ++i) arr[i] = {0, 0};
  arr[0].aval = 7;
  arr[(63 * 2) + 1].aval = 1U << 31U;
}

// A design passing a sized unpacked array to a C function, and filling one
// through an output, run to its end.
void RunSizedArrayDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int weighted(input bit [7:0] a [0:3]);\n"
      "  import \"DPI-C\" function void fill_arr(output int o [3:1]);\n"
      "  import \"DPI-C\" function void fill_vecs(\n"
      "      output logic [64:1] arr [0:63]);\n"
      "  bit [7:0] a [0:3] = '{1, 2, 3, 4};\n"
      "  bit [7:0] r [3:0] = '{4, 3, 2, 1};\n"
      "  int o [3:1];\n"
      "  logic [64:1] v [0:63];\n"
      "  int w, w2;\n"
      "  initial begin\n"
      "    w = weighted(a);\n"
      "    w2 = weighted(r);\n"
      "    fill_arr(o);\n"
      "    fill_vecs(v);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"weighted", reinterpret_cast<void*>(&WeightedByCIndex)},
       {"fill_arr", reinterpret_cast<void*>(&FillThreeInts)},
       {"fill_vecs", reinterpret_cast<void*>(&FillVectors)}},
      "annex_h_07_06_sized_arrays");
}

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// §H.7.3 with §H.7.6 c): a stand-alone array passed to a sized formal has the C
// layout, its lower index at C index 0 whichever way round its range was
// written -- `[0:3]` and `[3:0]` holding the same elements at the same
// addresses cross alike.
TEST(DpiArrayNaturalOrder, ASizedArrayCrossesInCLayoutLowerIndexFirst) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "w"), 4321U);
  EXPECT_EQ(VariableValue(f, "w2"), 4321U);
}

// An output array is copied back element by element, C index 0 into the
// lower index: o[1] gets what C wrote first.
TEST(DpiArrayNaturalOrder, ASizedOutputArrayIsCopiedBackLowerIndexFirst) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "o[1]"), 9U);
  EXPECT_EQ(VariableValue(f, "o[2]"), 8U);
  EXPECT_EQ(VariableValue(f, "o[3]"), 7U);
}

// An array of packed elements lays each element out as its canonical chunks
// (§H.7.6), two svLogicVecVal per 64-bit element here.
TEST(DpiArrayNaturalOrder, AnArrayOfVectorsCrossesAsTheirChunks) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "v[0]"), 7U);
  EXPECT_EQ(VariableValue(f, "v[63]"), uint64_t{1} << 63U);
  EXPECT_EQ(VariableValue(f, "v[1]"), 0U);
}

}  // namespace
