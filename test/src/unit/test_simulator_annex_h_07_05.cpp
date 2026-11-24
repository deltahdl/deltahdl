#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/svdpi.h"

namespace {

TEST(NormalizedLinearizedRanges, PackedPartIndexedFromLeastSignificantBit) {
  const int kN = 40;
  svBitVecVal vec[2] = {0u, 0u};

  svPutBitselBit(vec, 0, 1);
  svPutBitselBit(vec, kN - 1, 1);

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kN - 1), 1u);

  EXPECT_EQ(vec[0], 1u);
  EXPECT_EQ(vec[1], 1u << 7);
}

TEST(NormalizedLinearizedRanges, LinearizedReferenceFollowsRowMajorFormula) {
  const int kI = 2, kJ = 3, kK = 4;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  EXPECT_EQ(linear(1, 2, 3), 23);
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 2, 2), 1);
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 1, 3), kK);
  EXPECT_EQ(linear(1, 2, 3) - linear(0, 2, 3), kJ * kK);

  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, linear(1, 1, 2), 1);
  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), b == 18 ? 1u : 0u);
  }
}

TEST(NormalizedLinearizedRanges, RowMajorIterationIsContiguousOneDimensional) {
  const int kI = 2, kJ = 3, kK = 4;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  int counter = 0;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      for (int n = 0; n < kK; ++n) {
        EXPECT_EQ(linear(l, m, n), counter);
        svPutBitselBit(&vec, linear(l, m, n), counter & 1);
        ++counter;
      }
    }
  }
  EXPECT_EQ(counter, kI * kJ * kK);

  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), static_cast<svBit>(b & 1));
  }
}

TEST(NormalizedLinearizedRanges, LinearizedIndexCrossesCanonicalWordBoundary) {
  const int kJ = 2, kK = 20;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec[3] = {0u, 0u, 0u};

  const int kIdxLo = linear(0, 1, 12);
  EXPECT_EQ(kIdxLo, 32);
  svPutBitselBit(vec, kIdxLo, 1);
  EXPECT_EQ(vec[0], 0u);
  EXPECT_EQ(vec[1], 1u);

  const int kIdxHi = linear(1, 1, 19);
  EXPECT_EQ(kIdxHi, 79);
  svPutBitselBit(vec, kIdxHi, 1);
  EXPECT_EQ(vec[2], 1u << 15);

  EXPECT_EQ(svGetBitselBit(vec, kIdxLo), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kIdxHi), 1u);
}

TEST(NormalizedLinearizedRanges, LinearizedElementFieldAccessedByPartSelect) {
  const int kI = 2, kJ = 3, kK = 4;
  auto row_offset = [&](int l, int m) { return m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  svBitVecVal value = 1u;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      svPutPartselBit(&vec, value, row_offset(l, m), kK);
      ++value;
    }
  }

  value = 1u;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      svBitVecVal out = 0u;
      svGetPartselBit(&out, &vec, row_offset(l, m), kK);
      EXPECT_EQ(out, value & SV_MASK(kK));
      ++value;
    }
  }
}

TEST(NormalizedLinearizedRanges,
     FourStateLinearizedAccessPreservesLogicValues) {
  const int kI = 2, kJ = 2, kK = 3;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svLogicVecVal vec = {0u, 0u};
  svPutBitselLogic(&vec, linear(0, 0, 0), sv_1);
  svPutBitselLogic(&vec, linear(0, 1, 2), sv_z);
  svPutBitselLogic(&vec, linear(1, 0, 1), sv_x);
  svPutBitselLogic(&vec, linear(1, 1, 2), sv_0);

  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 0, 0)), sv_1);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 1, 2)), sv_z);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 0, 1)), sv_x);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 1, 2)), sv_0);

  for (int b = 0; b < kI * kJ * kK; ++b) {
    const bool kWritten = b == linear(0, 0, 0) || b == linear(0, 1, 2) ||
                          b == linear(1, 0, 1) || b == linear(1, 1, 2);
    if (!kWritten) {
      EXPECT_EQ(svGetBitselLogic(&vec, b), sv_0);
    }
  }
}

void SeePacked(const svBitVecVal* v) { SeeInC({v[0] & 0xFFFFFFU}); }

void SeeElements(const svLogicVecVal* b) {
  const svLogicVecVal& set = b[(2 * 32) + 5];
  const svLogicVecVal& plain = b[(9 * 32) + 31];
  SeeInC({set.aval & 0x3FFFFU, set.bval & 0x3FFFFU, plain.aval & 0x3FFFFU,
          plain.bval & 0x3FFFFU});
}

struct ArrayOfRows {
  int first;
  svBitVecVal b[4][2];
  int last;
};

void SeeRows(const ArrayOfRows* s) {
  SeeInC({s->first, s->b[2][0], s->b[2][1] & 0xFFFFU, s->b[1][0], s->last});
}

void WritePacked(svBitVecVal* v) { v[0] = 1U << 18U; }

void ShiftPacked(svBitVecVal* v) { v[0] = (v[0] & 0xFFFFFFU) << 1U; }

void CallWithPacked() {
  auto take =
      NamedExport<void (*)(const svBitVecVal*, svBitVecVal*)>("sv_take_packed");
  if (take == nullptr) return;
  const svBitVecVal kIn = 1U << 18U;
  svBitVecVal out = 0U;
  take(&kIn, &out);
  SeeInC({out & 0xFFFFFFU});
}

void RunPacked(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"see_packed", CAddress(&SeePacked)},
                  {"see_elements", CAddress(&SeeElements)},
                  {"see_rows", CAddress(&SeeRows)},
                  {"write_packed", CAddress(&WritePacked)},
                  {"shift_packed", CAddress(&ShiftPacked)},
                  {"call_export", CAddress(&CallWithPacked)}},
                 "annex_h_07_05_packed");
}

TEST(DpiLinearizedPackedPart, TwoDimensionsCrossRowMajor) {
  SimFixture f;
  RunPacked(
      "  import \"DPI-C\" function void see_packed(input bit [1:0][3:0] v);\n"
      "  bit [1:0][3:0] v = {4'h1, 4'h2};\n"
      "  initial see_packed(v);\n",
      f);
  ASSERT_EQ(SeenInC().size(), 1U);
  EXPECT_EQ(SeenInC()[0] & 0xFF, 0x12);
}

TEST(DpiLinearizedPackedPart, ThreeDimensionsCrossRowMajor) {
  SimFixture f;
  RunPacked(
      "  import \"DPI-C\" function void see_packed(\n"
      "      input bit [1:0][2:0][3:0] m);\n"
      "  bit [1:0][2:0][3:0] m;\n"
      "  initial begin m[1][1][2] = 1; see_packed(m); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1 << 18}));
}

TEST(DpiLinearizedPackedPart, AnUnpackedArraysElementsAreLinearizedEach) {
  SimFixture f;
  RunPacked(
      "  import \"DPI-C\" function void see_elements(\n"
      "      input logic [2:3][1:3][2:0] b [1:10][31:0]);\n"
      "  logic [2:3][1:3][2:0] b [1:10][31:0];\n"
      "  initial begin\n"
      "    foreach (b[i, j]) b[i][j] = 18'd1;\n"
      "    b[3][5] = 18'd0;\n"
      "    b[3][5][3][2][1] = 1'bx;\n"
      "    b[3][5][2][1][2] = 1'b1;\n"
      "    see_elements(b);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{(1 << 17) + (1 << 4), 1 << 4, 1, 0}));
}

TEST(DpiLinearizedPackedPart, AStructMembersElementsAreLinearizedEach) {
  SimFixture f;
  RunPacked(
      "  typedef struct { int first; bit [6:1][1:8] b [3:0]; int last; } s_t;\n"
      "  import \"DPI-C\" function void see_rows(input s_t s);\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    s.first = 3; s.last = 9;\n"
      "    s.b[2] = 48'h00a5_0000_0000;\n"
      "    s.b[1] = 48'h0000_0000_0017;\n"
      "    see_rows(s);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{3, 0, 0xA5, 0x17, 9}));
}

TEST(DpiLinearizedPackedPart, AStructMembersInnerRowLiesByItsIndex) {
  SimFixture f;
  RunPacked(
      "  typedef struct { int first; bit [6:1][1:8] b [3:0]; int last; } s_t;\n"
      "  import \"DPI-C\" function void see_rows(input s_t s);\n"
      "  s_t s;\n"
      "  bit [6:1][1:8] row;\n"
      "  initial begin\n"
      "    s.first = 3; s.last = 9;\n"
      "    row[5] = 8'ha5; s.b[2] = row;\n"
      "    see_rows(s);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{3, 0, 0xA5, 0, 9}));
}

TEST(DpiLinearizedPackedPart, AnOutputAndAnInoutLandInTheirElements) {
  SimFixture f;
  RunPacked(
      "  import \"DPI-C\" function void write_packed(\n"
      "      output bit [1:0][2:0][3:0] m);\n"
      "  import \"DPI-C\" function void shift_packed(\n"
      "      inout bit [1:0][2:0][3:0] m);\n"
      "  bit [1:0][2:0][3:0] m, k;\n"
      "  int written, set, shifted, was;\n"
      "  initial begin\n"
      "    write_packed(m); written = m[1][1]; set = m;\n"
      "    k[0][2][3] = 1; shift_packed(k); shifted = k[1][0]; was = k[0][2];\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "written"), 4U);
  EXPECT_EQ(DesignValue(f, "set"), 1U << 18U);
  EXPECT_EQ(DesignValue(f, "shifted"), 1U);
  EXPECT_EQ(DesignValue(f, "was"), 0U);
}

TEST(DpiLinearizedPackedPart, AnExportsFormalsCrossRowMajorToo) {
  SimFixture f;
  RunPacked(
      "  import \"DPI-C\" context function void call_export();\n"
      "  export \"DPI-C\" function sv_take_packed;\n"
      "  int got;\n"
      "  function void sv_take_packed(input bit [1:0][2:0][3:0] m,\n"
      "      output bit [1:0][2:0][3:0] o);\n"
      "    bit [1:0][2:0][3:0] seen, given;\n"
      "    seen = m;\n"
      "    got = seen[1][1];\n"
      "    given = 0;\n"
      "    given[1][2][3] = 1;\n"
      "    o = given;\n"
      "  endfunction\n"
      "  initial call_export();\n",
      f);
  EXPECT_EQ(DesignValue(f, "got"), 4U);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1 << 23}));
}

}  // namespace
