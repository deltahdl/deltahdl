#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

std::vector<SvActualDimension> ThreeByFour() { return {{3, 1}, {2, 5}}; }

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

TEST(DpiUnpackedArrayLayout, AnOpenArrayIsPassedByHandleInstead) {
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kInput), true),
      "const svOpenArrayHandle");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kOutput, 18), true),
            "const svOpenArrayHandle");
}

}  // namespace
