#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "simulator/svdpi.h"
#include "simulator/svdpi_sv31a.h"

namespace {

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

TEST(Sv31aDefinitions, TheSizeOfAPackedArrayFollowsItsWidth) {
  EXPECT_EQ(svSizeOfBitPackedArr(8), 4);
  EXPECT_EQ(svSizeOfBitPackedArr(33), 8);
  EXPECT_EQ(svSizeOfLogicPackedArr(8), 8);
  EXPECT_EQ(svSizeOfLogicPackedArr(64), 16);
  EXPECT_EQ(svSizeOfBitPackedArr(0), 0);
}

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

TEST(Sv31aDefinitions, ABitArrayOfWholeChunksIsCopiedWithoutAnother) {
  svBitVecVal actual[3] = {0x11111111u, 0x22222222u, 0x33333333u};
  const svBitVec32 kIn[3] = {0xDEADBEEFu, 0x8000005Au, 0x77777777u};
  svPutBitVec32(actual, kIn, 32);
  EXPECT_EQ(actual[0], 0xDEADBEEFu);
  EXPECT_EQ(actual[1], 0x22222222u);
  svPutBitVec32(actual, kIn, 64);
  EXPECT_EQ(actual[1], 0x8000005Au);
  EXPECT_EQ(actual[2], 0x33333333u);

  svBitVec32 out[3] = {1u, 2u, 3u};
  svGetBitVec32(out, actual, 32);
  EXPECT_EQ(out[0], 0xDEADBEEFu);
  EXPECT_EQ(out[1], 2u);
  svGetBitVec32(out, actual, 64);
  EXPECT_EQ(out[1], 0x8000005Au);
  EXPECT_EQ(out[2], 3u);
}

TEST(Sv31aDefinitions, ASelectPastTheFirstChunkChangesItsOwnBitOnly) {
  svBitVecVal bits[3] = {0u, 0xFFFFFFFFu, 0u};
  svPutSelectBit(bits, 37, sv_0);
  EXPECT_EQ(bits[0], 0u);
  EXPECT_EQ(bits[1], 0xFFFFFFDFu);
  EXPECT_EQ(bits[2], 0u);
  svPutSelectBit(bits, 64, sv_1);
  EXPECT_EQ(bits[0], 0u);
  EXPECT_EQ(bits[1], 0xFFFFFFDFu);
  EXPECT_EQ(bits[2], 1u);
  EXPECT_EQ(svGetSelectBit(bits, 37), sv_0);

  svLogicVecVal logic[2] = {{0u, 0u}, {0u, 0u}};
  svPutSelectLogic(logic, 37, sv_x);
  svPutSelectLogic(logic, 32, sv_z);
  svPutSelectLogic(logic, 63, sv_1);
  EXPECT_EQ(logic[0].aval, 0u);
  EXPECT_EQ(logic[0].bval, 0u);
  EXPECT_EQ(logic[1].aval, 0x80000020u);
  EXPECT_EQ(logic[1].bval, 0x00000021u);
  EXPECT_EQ(svGetSelectLogic(logic, 37), sv_x);
  EXPECT_EQ(svGetSelectLogic(logic, 32), sv_z);
}

TEST(Sv31aDefinitions, ABitPartSelectTakesAWholeChunk) {
  svBitVecVal bits[3] = {0x89ABCDEFu, 0x01234567u, 0xFEDCBA98u};
  svBitVec32 chunk = 0;
  svGetPartSelectBit(&chunk, bits, 32, 32);
  EXPECT_EQ(chunk, 0x01234567u);
  svGetPartSelectBit(&chunk, bits, 4, 32);
  EXPECT_EQ(chunk, 0x789ABCDEu);
  svPutPartSelectBit(bits, 0xC0FFEE42u, 32, 32);
  EXPECT_EQ(bits[0], 0x89ABCDEFu);
  EXPECT_EQ(bits[1], 0xC0FFEE42u);
  EXPECT_EQ(bits[2], 0xFEDCBA98u);
  svPutPartSelectBit(bits, 0x12345678u, 4, 32);
  EXPECT_EQ(bits[0], 0x2345678Fu);
  EXPECT_EQ(bits[1], 0xC0FFEE41u);
}

TEST(Sv31aDefinitions, ALogicPartSelectTakesAWholeChunk) {
  svLogicVecVal logic[2] = {{0x89ABCDEFu, 0x0F0F0F0Fu},
                            {0x01234567u, 0xF0F0F0F0u}};
  svLogicVec32 chunk = {0u, 0u};
  svGetPartSelectLogic(&chunk, logic, 32, 32);
  EXPECT_EQ(chunk.c, 0x01234567u);
  EXPECT_EQ(chunk.d, 0xF0F0F0F0u);
  svGetPartSelectLogic(&chunk, logic, 4, 32);
  EXPECT_EQ(chunk.c, 0x789ABCDEu);
  EXPECT_EQ(chunk.d, 0x00F0F0F0u);
  const svLogicVec32 kAligned = {0xC0FFEE42u, 0x00FF00FFu};
  svPutPartSelectLogic(logic, kAligned, 32, 32);
  EXPECT_EQ(logic[0].aval, 0x89ABCDEFu);
  EXPECT_EQ(logic[1].aval, 0xC0FFEE42u);
  EXPECT_EQ(logic[1].bval, 0x00FF00FFu);
  const svLogicVec32 kUnaligned = {0x12345678u, 0x87654321u};
  svPutPartSelectLogic(logic, kUnaligned, 4, 32);
  EXPECT_EQ(logic[0].aval, 0x2345678Fu);
  EXPECT_EQ(logic[0].bval, 0x7654321Fu);
  EXPECT_EQ(logic[1].aval, 0xC0FFEE41u);
  EXPECT_EQ(logic[1].bval, 0x00FF00F8u);
}

TEST(Sv31aDefinitions, APartSelectCrossesAChunkBoundary) {
  svBitVecVal bits[2] = {0x01234567u, 0x89ABCDEFu};
  svPutPartSelectBit(bits, 0xA5u, 28, 8);
  EXPECT_EQ(bits[0], 0x51234567u);
  EXPECT_EQ(bits[1], 0x89ABCDEAu);

  const svLogicVecVal kLogic[2] = {{0x51234567u, 0xC0000000u},
                                   {0x89ABCDEAu, 0x00000003u}};
  svLogicVecVal logic[2] = {kLogic[0], kLogic[1]};
  svLogicVec32 slice = {0u, 0u};
  svGetPartSelectLogic(&slice, logic, 28, 8);
  EXPECT_EQ(slice.c, 0xA5u);
  EXPECT_EQ(slice.d, 0x3Cu);
}

}  // namespace
