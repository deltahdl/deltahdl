#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.11.4 (Direct access to unpacked arrays): an unpacked array formal
// that is not an open array has the same layout a C compiler uses and is
// accessed by C indexing, the mapping of §H.7.6. The cases check the C
// declaration such a formal takes, that a packed element becomes one more
// dimension of canonical chunks, that a SystemVerilog index maps to the C
// index counted from the low bound whichever way the range runs, that the
// elements lie in row-major order the last dimension varying fastest and
// sizeof the element apart, that the offset so computed is the one a C
// compiler gives the same array, and that an open array is the exception,
// passed by handle.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// `int a [3:1][2:5]`: two unpacked dimensions of 3 and 4 elements.
std::vector<SvActualDimension> ThreeByFour() { return {{3, 1}, {2, 5}}; }

// §H.11.4: `int a [3:1][2:5]` is declared to C as int a[3][4], the sizes the
// counts of the ranges in declaration order, const for an input as §H.8.7
// has every input and without for an output or inout.
TEST(DpiUnpackedArrayLayout, ASizedUnpackedFormalIsACArrayOfItsElementType) {
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kInt, Direction::kInput), ThreeByFour()),
            "const int a[3][4]");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kInt, Direction::kOutput), ThreeByFour()),
            "int a[3][4]");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kByte, Direction::kInout), {{-1, -8}}),
            "char a[8]");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kStruct, Direction::kInput), {{0, 1}}),
            "");
}

// §H.11.4 with §H.7.7: a packed element is its canonical chunk array, so the
// C array carries one more dimension of ceil(width/32) chunks after the
// unpacked ones -- §H.7.6's `logic [17:0] b [1:10][31:0]` is svLogicVecVal
// b[10][32][1], and a 64-bit 2-state element takes two svBitVecVal.
TEST(DpiUnpackedArrayLayout, APackedElementIsOneMoreDimensionOfChunks) {
  DpiArg b = Formal(DataTypeKind::kLogic, Direction::kInput, 18);
  b.name = "b";
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(b, {{1, 10}, {31, 0}}),
            "const svLogicVecVal b[10][32][1]");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kBit, Direction::kOutput, 64), {{0, 1}}),
            "svBitVecVal a[2][2]");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal(DataTypeKind::kTime, Direction::kInput), {{2, 0}}),
            "const svLogicVecVal a[3][2]");
}

// §H.11.4: the element is sizeof its C type apart from the next, which is
// what the C compiler's layout puts between them.
TEST(DpiUnpackedArrayLayout, AnElementIsSizeofItsCType) {
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kByte, Direction::kInput)),
            1U);
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kInt, Direction::kInput)),
            sizeof(int));
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kLongint, Direction::kInput)),
            sizeof(long long));
  EXPECT_EQ(
      DpiCElementBytes(Formal(DataTypeKind::kShortreal, Direction::kInput)),
      sizeof(float));
  EXPECT_EQ(
      DpiCElementBytes(Formal(DataTypeKind::kLogic, Direction::kInput, 18)),
      sizeof(SvLogicVecVal));
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kBit, Direction::kInput, 64)),
            2 * sizeof(SvBitVecVal));
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kInteger, Direction::kInput)),
            sizeof(SvLogicVecVal));
  EXPECT_EQ(DpiCElementBytes(Formal(DataTypeKind::kStruct, Direction::kInput)),
            0U);
}

// §H.11.4 with §H.7.6 c): C indexing counts each dimension from 0 at the
// low bound of its range, whichever way the range runs, so in
// `int a [3:1][2:5]` the element a[1][2] is C's a[0][0], a[3][5] is a[2][3]
// and a[3][2] is a[2][0]; a range over negative indices counts from its low
// bound the same way.
TEST(DpiUnpackedArrayLayout, ASystemVerilogIndexCountsFromTheLowBound) {
  using Indices = std::vector<uint32_t>;
  EXPECT_EQ(DpiCIndicesOfUnpackedElement(ThreeByFour(), {1, 2}),
            (Indices{0, 0}));
  EXPECT_EQ(DpiCIndicesOfUnpackedElement(ThreeByFour(), {3, 5}),
            (Indices{2, 3}));
  EXPECT_EQ(DpiCIndicesOfUnpackedElement(ThreeByFour(), {3, 2}),
            (Indices{2, 0}));
  EXPECT_EQ(DpiCIndicesOfUnpackedElement({{-1, -8}}, {-8}), (Indices{0}));
  EXPECT_EQ(DpiCIndicesOfUnpackedElement({{-1, -8}}, {-1}), (Indices{7}));
}

// §H.11.4: the elements lie as a C compiler lays them out, in row-major
// order with the last dimension varying fastest, so in `int a [3:1][2:5]`
// one step along the second dimension moves sizeof(int) and one along the
// first moves four of them; laid out column-major instead, a[1][3] would sit
// three rows in.
TEST(DpiUnpackedArrayLayout, ElementsLieRowMajorTheLastDimensionFastest) {
  const DpiArg kInt = Formal(DataTypeKind::kInt, Direction::kInput);
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kInt, ThreeByFour(), {1, 2}), 0U);
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kInt, ThreeByFour(), {1, 3}),
            sizeof(int));
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kInt, ThreeByFour(), {2, 2}),
            4 * sizeof(int));
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kInt, ThreeByFour(), {3, 5}),
            11 * sizeof(int));
  const DpiArg kLogic = Formal(DataTypeKind::kLogic, Direction::kInput, 18);
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kLogic, {{1, 10}, {31, 0}}, {2, 0}),
            32 * sizeof(SvLogicVecVal));
}

// §H.11.4: the layout is the C compiler's own, so the offset the model gives
// an element of `int a [3:1][2:5]` is where the compiler places it in
// int a[3][4], and likewise for svLogicVecVal b[2][3][1].
TEST(DpiUnpackedArrayLayout, TheOffsetIsWhereTheCCompilerPlacesTheElement) {
  int a[3][4] = {};
  const char* const kBase = reinterpret_cast<const char*>(&a[0][0]);
  const DpiArg kInt = Formal(DataTypeKind::kInt, Direction::kInput);
  for (int32_t i = 1; i <= 3; ++i) {
    for (int32_t j = 2; j <= 5; ++j) {
      const auto kCompiler = static_cast<std::size_t>(
          reinterpret_cast<const char*>(&a[i - 1][j - 2]) - kBase);
      EXPECT_EQ(DpiCOffsetOfUnpackedElement(kInt, ThreeByFour(), {i, j}),
                kCompiler)
          << i << " " << j;
    }
  }
  SvLogicVecVal b[2][3][1] = {};
  const char* const kBaseB = reinterpret_cast<const char*>(&b[0][0][0]);
  const DpiArg kLogic = Formal(DataTypeKind::kLogic, Direction::kInput, 18);
  const std::vector<SvActualDimension> kDims{{5, 4}, {0, 2}};
  EXPECT_EQ(DpiCOffsetOfUnpackedElement(kLogic, kDims, {5, 1}),
            static_cast<std::size_t>(
                reinterpret_cast<const char*>(&b[1][1][0]) - kBaseB));
}

// §H.11.4's exception: an open array formal is passed by the handle of
// §H.8.6 whatever its type, and its elements are reached through the
// functions of §H.12 rather than by C indexing.
TEST(DpiUnpackedArrayLayout, AnOpenArrayIsPassedByHandleInstead) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), true),
      "const svOpenArrayHandle");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kOutput, 18), true),
            "const svOpenArrayHandle");
}

}  // namespace
