#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

// svdpi_sv31a.h is the companion of svdpi.h, so this file includes it alone
// as the svdpi.h cases do: the two redefine VPI names vpi.h spells otherwise.
#include "simulator/svdpi_sv31a.h"

namespace {

// §H.14.2: the definitions of SV3.1a-style canonical access to packed data
// -- SV_CANONICAL_SIZE counting 32-bit chunks, svBitVec32 a chunk of a bit
// array and svLogicVec32 a chunk of a logic array with its c and d words --
// and the opaque references to a standalone packed array, void pointers.
TEST(Sv31aDefinitions, TheCanonicalChunkTypesAndReferencesAreDefined) {
  EXPECT_EQ(SV_CANONICAL_SIZE(1), 1);
  EXPECT_EQ(SV_CANONICAL_SIZE(32), 1);
  EXPECT_EQ(SV_CANONICAL_SIZE(33), 2);
  EXPECT_EQ(SV_CANONICAL_SIZE(64), 2);
  EXPECT_TRUE((std::is_same<svBitVec32, uint32_t>::value));
  EXPECT_EQ(sizeof(svLogicVec32), 2 * sizeof(unsigned int));
  svLogicVec32 chunk = {1u, 2u};
  EXPECT_EQ(chunk.c, 1u);
  EXPECT_EQ(chunk.d, 2u);
  EXPECT_TRUE((std::is_same<svBitPackedArrRef, void*>::value));
  EXPECT_TRUE((std::is_same<svLogicPackedArrRef, void*>::value));
}

// §H.14.2: the total size in bytes of the simulator's representation of a
// packed array of a width -- one 32-bit chunk per 32 bits of a bit array and
// one aval/bval pair per 32 bits of a logic array under this simulator.
TEST(Sv31aDefinitions, TheSizeOfAPackedArrayFollowsItsWidth) {
  EXPECT_EQ(svSizeOfBitPackedArr(8), 4);
  EXPECT_EQ(svSizeOfBitPackedArr(33), 8);
  EXPECT_EQ(svSizeOfLogicPackedArr(8), 8);
  EXPECT_EQ(svSizeOfLogicPackedArr(64), 16);
  EXPECT_EQ(svSizeOfBitPackedArr(0), 0);
}

// §H.14.2: the translation functions copy the whole array in either
// direction between the actual representation and a canonical buffer the
// user allocates for the width, a 40-bit bit array in two chunks each way.
TEST(Sv31aDefinitions, TheBitArrayIsCopiedWholeInEitherDirection) {
  svBitVecVal actual[2] = {0, 0};
  const svBitVec32 kIn[2] = {0xDEADBEEFu, 0x5Au};
  svPutBitVec32(actual, kIn, 40);
  EXPECT_EQ(actual[0], 0xDEADBEEFu);
  EXPECT_EQ(actual[1], 0x5Au);
  svBitVec32 out[2] = {0, 0};
  svGetBitVec32(out, actual, 40);
  EXPECT_EQ(out[0], 0xDEADBEEFu);
  EXPECT_EQ(out[1], 0x5Au);
}

// §H.14.2: a logic array's chunks carry the c and d words modeled upon the
// PLI's avalue and bvalue, copied whole each way for a 33-bit array.
TEST(Sv31aDefinitions, TheLogicArrayIsCopiedWholeInEitherDirection) {
  svLogicVecVal actual[2] = {{0, 0}, {0, 0}};
  const svLogicVec32 kIn[2] = {{0x0F0F0F0Fu, 0xF0F0F0F0u}, {1u, 1u}};
  svPutLogicVec32(actual, kIn, 33);
  EXPECT_EQ(actual[0].aval, 0x0F0F0F0Fu);
  EXPECT_EQ(actual[0].bval, 0xF0F0F0F0u);
  EXPECT_EQ(actual[1].aval, 1u);
  EXPECT_EQ(actual[1].bval, 1u);
  svLogicVec32 out[2] = {{0, 0}, {0, 0}};
  svGetLogicVec32(out, actual, 33);
  EXPECT_EQ(out[0].c, 0x0F0F0F0Fu);
  EXPECT_EQ(out[0].d, 0xF0F0F0F0u);
  EXPECT_EQ(out[1].c, 1u);
  EXPECT_EQ(out[1].d, 1u);
}

// §H.14.2: bit-select processing on the actual representation, indexed
// n-1:0 with 0 the LSB -- a bit read and written by its index, and a logic
// read and written with its four-state value.
TEST(Sv31aDefinitions, BitSelectsReadAndWriteTheActualRepresentation) {
  svBitVecVal bits[2] = {0x00000001u, 0x80000000u};
  EXPECT_EQ(svGetSelectBit(bits, 0), sv_1);
  EXPECT_EQ(svGetSelectBit(bits, 1), sv_0);
  EXPECT_EQ(svGetSelectBit(bits, 63), sv_1);
  svPutSelectBit(bits, 1, sv_1);
  svPutSelectBit(bits, 0, sv_0);
  EXPECT_EQ(bits[0], 0x00000002u);

  svLogicVecVal logic[1] = {{0, 0}};
  svPutSelectLogic(logic, 3, sv_x);
  svPutSelectLogic(logic, 2, sv_z);
  svPutSelectLogic(logic, 1, sv_1);
  EXPECT_EQ(svGetSelectLogic(logic, 3), sv_x);
  EXPECT_EQ(svGetSelectLogic(logic, 2), sv_z);
  EXPECT_EQ(svGetSelectLogic(logic, 1), sv_1);
  EXPECT_EQ(svGetSelectLogic(logic, 0), sv_0);
}

// §H.14.2: a part-select of up to 32 bits copies the implementation part
// [w+i-1:i] to the canonical chunk part [w-1:0] and back -- read as a chunk,
// as 32 bits and as 64 bits from a starting index, and written in place.
TEST(Sv31aDefinitions, PartSelectsCopyANarrowSliceEachWay) {
  svBitVecVal bits[3] = {0x89ABCDEFu, 0x01234567u, 0xFFu};
  svBitVec32 chunk = 0;
  svGetPartSelectBit(&chunk, bits, 4, 8);
  EXPECT_EQ(chunk, 0xDEu);
  EXPECT_EQ(svGetBits(bits, 28, 8), 0x78u);
  EXPECT_EQ(svGet32Bits(bits, 16), 0x456789ABu);
  EXPECT_EQ(svGet64Bits(bits, 8), 0xFF01234567'89ABCDull);

  svPutPartSelectBit(bits, 0x5u, 4, 4);
  EXPECT_EQ(bits[0], 0x89ABCD5Fu);

  svLogicVecVal logic[2] = {{0x0000FF00u, 0x000000FFu}, {0, 0}};
  svLogicVec32 slice = {0, 0};
  svGetPartSelectLogic(&slice, logic, 4, 8);
  EXPECT_EQ(slice.c, 0xF0u);
  EXPECT_EQ(slice.d, 0x0Fu);
  const svLogicVec32 kZs = {0x0u, 0xFu};
  svPutPartSelectLogic(logic, kZs, 28, 8);
  EXPECT_EQ(svGetSelectLogic(logic, 28), sv_z);
  EXPECT_EQ(svGetSelectLogic(logic, 31), sv_z);
  EXPECT_EQ(svGetSelectLogic(logic, 32), sv_0);
}

}  // namespace
