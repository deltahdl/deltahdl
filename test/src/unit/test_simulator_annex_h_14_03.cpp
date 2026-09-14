#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_src.h"

using namespace delta;

namespace {

// §H.14.3: svdpi_src.h defines two symbols only, and an application that
// does not need it is binary compatible while one that uses it is compiled
// for each simulator it runs on.
TEST(SvdpiSrcIncludeFile, TwoSymbolsDecideBinaryOrSourceCompatibility) {
  EXPECT_EQ(DpiSvdpiSrcSymbolCount(), 2u);
  EXPECT_EQ(DpiCompatibilityOfApplication(false),
            DpiApplicationCompatibility::kBinary);
  EXPECT_EQ(DpiCompatibilityOfApplication(true),
            DpiApplicationCompatibility::kSource);
  EXPECT_FALSE(DpiApplicationIsRecompiledPerSimulator(false));
  EXPECT_TRUE(DpiApplicationIsRecompiledPerSimulator(true));
}

// §H.14.3: the macros declare variables representing packed arrays of bit
// and of logic, and neither defines an array type -- each variable is a
// struct of the width's chunks, sized as the simulator's representation.
TEST(SvdpiSrcIncludeFile, TheMacrosDeclareNoArrayType) {
  EXPECT_FALSE(DpiPackedArrayMacroMayDefineAnArrayType());
  SV_BIT_PACKED_ARRAY(40, bits);
  SV_LOGIC_PACKED_ARRAY(64, logic);
  EXPECT_FALSE(std::is_array<decltype(bits)>::value);
  EXPECT_FALSE(std::is_array<decltype(logic)>::value);
  EXPECT_EQ(sizeof(bits), static_cast<size_t>(svSizeOfBitPackedArr(40)));
  EXPECT_EQ(sizeof(logic), static_cast<size_t>(svSizeOfLogicPackedArr(64)));
}

// §H.14.3 with §H.14.2: a variable the macro declares is what the SV3.1a
// functions take a reference to -- written whole from a canonical buffer and
// read back bit by bit.
TEST(SvdpiSrcIncludeFile, ADeclaredVariableIsAPackedArrayReference) {
  SV_BIT_PACKED_ARRAY(40, bits);
  const svBitVec32 kIn[2] = {0x00000005u, 0x80u};
  svPutBitVec32(&bits, kIn, 40);
  EXPECT_EQ(svGetSelectBit(&bits, 0), sv_1);
  EXPECT_EQ(svGetSelectBit(&bits, 1), sv_0);
  EXPECT_EQ(svGetSelectBit(&bits, 2), sv_1);
  EXPECT_EQ(svGetSelectBit(&bits, 39), sv_1);

  SV_LOGIC_PACKED_ARRAY(8, logic);
  const svLogicVec32 kZ = {0x0u, 0x1u};
  svPutLogicVec32(&logic, &kZ, 8);
  EXPECT_EQ(svGetSelectLogic(&logic, 0), sv_z);
  EXPECT_EQ(svGetSelectLogic(&logic, 1), sv_0);
}

}  // namespace
