#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

namespace {

TEST(PackedArrayCanonicalRepresentation, ElementCarrierWidths) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
  EXPECT_EQ(sizeof(delta::SvBitVecVal), sizeof(svBitVecVal));
  EXPECT_EQ(sizeof(delta::SvLogicVecVal), sizeof(svLogicVecVal));
}

TEST(PackedArrayCanonicalRepresentation, LogicVecValIsVpiVecval) {
  static_assert(std::is_same<svLogicVecVal, s_vpi_vecval>::value,
                "svLogicVecVal must be the s_vpi_vecval type");

  s_vpi_vecval raw;
  raw.aval = 0x5u;
  raw.bval = 0x2u;

  const svLogicVecVal* as_logic = &raw;
  EXPECT_EQ(svGetBitselLogic(as_logic, 0), sv_1);
  EXPECT_EQ(svGetBitselLogic(as_logic, 1), sv_z);
  EXPECT_EQ(svGetBitselLogic(as_logic, 2), sv_1);
}

TEST(PackedArrayCanonicalRepresentation, GroupedInto32BitElements) {
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(32), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(65), 3);

  svBitVecVal vec[2] = {0u, 0u};
  svPutBitselBit(vec, 40, 1);
  EXPECT_EQ(vec[0], 0u);
  EXPECT_EQ(vec[1], 1u << 8);
  EXPECT_EQ(svGetBitselBit(vec, 40), 1u);
}

TEST(PackedArrayCanonicalRepresentation,
     FirstElementHoldsLeastSignificantBits) {
  svBitVecVal vec[2] = {0u, 0u};
  svPutBitselBit(vec, 0, 1);
  svPutBitselBit(vec, 32, 1);
  EXPECT_EQ(vec[0], 1u);
  EXPECT_EQ(vec[1], 1u);

  svLogicVecVal lvec[2] = {{0u, 0u}, {0u, 0u}};
  svPutBitselLogic(lvec, 0, sv_1);
  svPutBitselLogic(lvec, 33, sv_z);
  EXPECT_EQ(lvec[0].aval, 1u);
  EXPECT_EQ(lvec[0].bval, 0u);
  EXPECT_EQ(lvec[1].aval, 0u);
  EXPECT_EQ(lvec[1].bval, 1u << 1);
}

TEST(PackedArrayCanonicalRepresentation, UnusedBitsAreMaskedByConsumer) {
  svBitVecVal elem = 0xFFFFFFE9u;
  EXPECT_EQ(SV_MASK(5), 0x1Fu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(elem, 5), 0x09u);

  svBitVecVal high_bit_set = 0x1Fu;
  svBitVecVal high_bit_clear = 0x0Fu;
  int narrow_width = 4;
  EXPECT_EQ(SV_GET_SIGNED_BITS(high_bit_set, narrow_width), 0xFFFFFFFFu);
  EXPECT_EQ(SV_GET_SIGNED_BITS(high_bit_clear, narrow_width), 0x0Fu);
}

TEST(PackedArrayCanonicalRepresentation, PartSelectStraddlesElementBoundary) {
  svBitVecVal vec[2] = {0xF0000000u, 0x0000000Au};
  svBitVecVal out = 0u;
  svGetPartselBit(&out, vec, 28, 8);
  EXPECT_EQ(out, 0xAFu);
}

TEST(PackedArrayCanonicalRepresentation, FullWidthElementHasNoUnusedBits) {
  svBitVecVal full_elem = 0xDEADBEEFu;
  int full_width = 32;
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(full_elem, full_width), 0xDEADBEEFu);
  EXPECT_EQ(SV_GET_SIGNED_BITS(full_elem, full_width), 0xDEADBEEFu);
}

TEST(DpiCanonicalRepresentation, TwoStateInBitVecValFourStateInLogicVecVal) {
  using delta::DataTypeKind;
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kBit), "svBitVecVal");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kLogic),
            "svLogicVecVal");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kReg),
            "svLogicVecVal");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kInteger),
            "svLogicVecVal");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kTime),
            "svLogicVecVal");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kReal), "");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kString), "");
  EXPECT_EQ(delta::DpiCanonicalElementType(DataTypeKind::kStruct), "");
}

TEST(DpiCanonicalRepresentation, TheFirstElementHoldsTheLeastSignificantBits) {
  EXPECT_EQ(delta::kDpiCanonicalElementBits, 32U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(0).element, 0U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(0).bit, 0U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(31).element, 0U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(31).bit, 31U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(32).element, 1U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(32).bit, 0U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(70).element, 2U);
  EXPECT_EQ(delta::DpiCanonicalPositionOfBit(70).bit, 6U);
  svBitVecVal vec[3] = {0U, 0U, 0U};
  const delta::DpiCanonicalBitPosition kSeventy =
      delta::DpiCanonicalPositionOfBit(70);
  vec[kSeventy.element] = 1U << kSeventy.bit;
  EXPECT_EQ(svGetBitselBit(vec, 70), 1U);
}

TEST(DpiCanonicalRepresentation, TheLastElementCanHoldUnusedBits) {
  EXPECT_EQ(delta::DpiCanonicalUnusedBits(5), 27U);
  EXPECT_EQ(delta::DpiCanonicalUnusedBits(33), 31U);
  EXPECT_EQ(delta::DpiCanonicalUnusedBits(32), 0U);
  EXPECT_EQ(delta::DpiCanonicalUnusedBits(64), 0U);
  EXPECT_EQ(delta::DpiCanonicalUnusedBits(18), 14U);
  EXPECT_EQ(delta::DpiCanonicalWordCount(5), 1U);
  EXPECT_EQ(delta::DpiCanonicalWordCount(33), 2U);
}

TEST(DpiCanonicalRepresentation, TheUserMasksOrSignExtendsTheUnusedBits) {
  const uint32_t kPositive = 0xFFFFFFE9U;
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(kPositive, 5, false),
            0x09U);
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(kPositive, 5, true),
            0x09U);
  const uint32_t kNegative = 0x00000019U;
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(kNegative, 5, false),
            0x19U);
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(kNegative, 5, true),
            0xFFFFFFF9U);
  EXPECT_EQ(
      delta::DpiCanonicalLastElementWithUnusedBits(0xFFFFFFFFU, 33, false), 1U);
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(0x1U, 33, true),
            0xFFFFFFFFU);
  EXPECT_EQ(delta::DpiCanonicalLastElementWithUnusedBits(0xDEADBEEFU, 32, true),
            0xDEADBEEFU);
  EXPECT_EQ(
      delta::DpiCanonicalLastElementWithUnusedBits(0xDEADBEEFU, 64, false),
      0xDEADBEEFU);
}

}  // namespace
