#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

// Annex H.7.7 - Canonical representation of packed arrays.
//
// H.7.7 defines the C-layer carriers for packed values: svBitVecVal for
// 2-state arrays and svLogicVecVal for 4-state arrays, with svLogicVecVal being
// equivalent to the VPI s_vpi_vecval type. A packed array is a sequence of
// 32-bit-wide elements, the first element holding the 32 least-significant bits
// and each successive element holding the next-more-significant group. The last
// element may contain unused bits whose contents are undetermined; the consumer
// is responsible for masking or sign-extending them. These tests observe those
// representation rules as applied by the svdpi.h carriers and the svdpi.cpp
// accessors.

namespace {

// C1: the canonical 2-state carrier is a single 32-bit element, and the 4-state
// carrier pairs two 32-bit words (aval/bval).
TEST(PackedArrayCanonicalRepresentation, ElementCarrierWidths) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
  // The internal runtime carriers mirror the same canonical element widths.
  EXPECT_EQ(sizeof(delta::SvBitVecVal), sizeof(svBitVecVal));
  EXPECT_EQ(sizeof(delta::SvLogicVecVal), sizeof(svLogicVecVal));
}

// C2: svLogicVecVal is fully equivalent to the VPI s_vpi_vecval carrier - it is
// the very same type, so a 4-state value written through one is observed
// identically through the other.
TEST(PackedArrayCanonicalRepresentation, LogicVecValIsVpiVecval) {
  static_assert(std::is_same<svLogicVecVal, s_vpi_vecval>::value,
                "svLogicVecVal must be the s_vpi_vecval type");

  s_vpi_vecval raw;
  raw.aval = 0x5u;  // bit0=1, bit2=1
  raw.bval = 0x2u;  // bit1 has the x/z flag

  const svLogicVecVal* as_logic = &raw;
  // bit0: aval=1,bval=0 -> 1 ; bit1: aval=0,bval=1 -> z ; bit2: aval=1,bval=0
  EXPECT_EQ(svGetBitselLogic(as_logic, 0), sv_1);
  EXPECT_EQ(svGetBitselLogic(as_logic, 1), sv_z);
  EXPECT_EQ(svGetBitselLogic(as_logic, 2), sv_1);
}

// C3: a packed array is grouped into 32-bit elements; the element count grows
// by one for every additional (partial) group of 32 bits.
TEST(PackedArrayCanonicalRepresentation, GroupedInto32BitElements) {
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(32), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(65), 3);

  // A bit beyond the first group is accessed in the second element: setting
  // global bit 40 must land in element[1], bit 8, leaving element[0] clear.
  svBitVecVal vec[2] = {0u, 0u};
  svPutBitselBit(vec, 40, 1);
  EXPECT_EQ(vec[0], 0u);
  EXPECT_EQ(vec[1], 1u << 8);
  EXPECT_EQ(svGetBitselBit(vec, 40), 1u);
}

// C4: the first element holds the 32 least-significant bits and each successive
// element holds the next-more-significant group.
TEST(PackedArrayCanonicalRepresentation,
     FirstElementHoldsLeastSignificantBits) {
  svBitVecVal vec[2] = {0u, 0u};
  svPutBitselBit(vec, 0, 1);   // least-significant bit of the whole array
  svPutBitselBit(vec, 32, 1);  // first bit of the next-more-significant group
  EXPECT_EQ(vec[0], 1u);       // LSBs live in element 0
  EXPECT_EQ(vec[1], 1u);       // bit 32 is bit 0 of element 1

  // 4-state arrays follow the same element ordering for both aval and bval.
  svLogicVecVal lvec[2] = {{0u, 0u}, {0u, 0u}};
  svPutBitselLogic(lvec, 0, sv_1);
  svPutBitselLogic(lvec, 33, sv_z);
  EXPECT_EQ(lvec[0].aval, 1u);
  EXPECT_EQ(lvec[0].bval, 0u);
  EXPECT_EQ(lvec[1].aval, 0u);
  EXPECT_EQ(lvec[1].bval, 1u << 1);  // bit 33 -> element 1, bit 1, z sets bval
}

// C5: the unused bits of the last element are undetermined - the carrier does
// not auto-clear them - and the consumer masks (or sign-extends) them using the
// provided utilities.
TEST(PackedArrayCanonicalRepresentation, UnusedBitsAreMaskedByConsumer) {
  // A 5-bit value stored in a 32-bit element alongside arbitrary upper bits.
  svBitVecVal elem = 0xFFFFFFE9u;  // low 5 bits = 0x09, upper 27 bits = garbage
  EXPECT_EQ(SV_MASK(5), 0x1Fu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(elem, 5), 0x09u);  // upper unused bits masked

  // Sign extension replicates the value's high bit across the unused bits.
  EXPECT_EQ(SV_GET_SIGNED_BITS(0x1Fu, 4), 0xFFFFFFFFu);  // high bit set -> -1
  EXPECT_EQ(SV_GET_SIGNED_BITS(0x0Fu, 4), 0x0Fu);        // high bit clear
}

// C4 edge case: a part-select whose window straddles the 32-bit element
// boundary must gather its low bits from the first element and its high bits
// from the next-more-significant element, proving the LSB-first word ordering
// across the whole array (svGetPartselBit's cross-word path).
TEST(PackedArrayCanonicalRepresentation, PartSelectStraddlesElementBoundary) {
  svBitVecVal vec[2] = {0xF0000000u, 0x0000000Au};
  // Bits 28..35: bits 28-31 are the top nibble of element 0 (0xF), bits 32-35
  // are the bottom nibble of element 1 (0xA), so the 8-bit window reads 0xAF.
  svBitVecVal out = 0u;
  svGetPartselBit(&out, vec, 28, 8);
  EXPECT_EQ(out, 0xAFu);
}

// C5 edge case: a full 32-bit element has no unused bits, so the masking and
// sign-extension utilities pass the element through unchanged (the width-32
// branch).
TEST(PackedArrayCanonicalRepresentation, FullWidthElementHasNoUnusedBits) {
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xDEADBEEFu, 32), 0xDEADBEEFu);
  EXPECT_EQ(SV_GET_SIGNED_BITS(0xDEADBEEFu, 32), 0xDEADBEEFu);
}

}  // namespace
