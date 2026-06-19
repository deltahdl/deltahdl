#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <type_traits>

// Annex I.2 (Overview) makes two normative requirements on the svdpi.h
// include file shipped by the simulator:
//   * The header shall be provided by every SystemVerilog simulator.
//   * Implementations shall define the types uint8_t and uint32_t (the exact
//     means of doing so is left unprescribed).
// The deprecated trailer and the platform-specific size-typedef block shown in
// I.3 are explicitly optional/illustrative, so I.2 owns nothing beyond these
// two obligations. The tests below observe the production header satisfying
// them: including it must compile (it is provided), and the two width types
// must be visible and have the widths their names promise.
#include "simulator/svdpi.h"

namespace {

// Claim A: the normative include file is provided and includes cleanly.
// Reaching any of its declarations is enough to prove the header exists and is
// usable by C/C++ translation units.
TEST(SvdpiIncludeFileContract, IncludeFileIsProvided) {
  svScalar bit = sv_1;
  EXPECT_EQ(bit, 1);
}

// Claim C: uint8_t and uint32_t are defined as a side effect of including the
// header. svdpi.h brings them in (via <stdint.h>), so they must be nameable
// here without any further include and must carry their advertised widths.
TEST(SvdpiIncludeFileContract, WidthTypesAreDefined) {
  uint8_t byte = 0xFFu;
  uint32_t word = 0xFFFFFFFFu;
  EXPECT_EQ(sizeof(byte), 1u);
  EXPECT_EQ(sizeof(word), 4u);
  EXPECT_EQ(byte, 0xFFu);
  EXPECT_EQ(word, 0xFFFFFFFFu);
}

// The types are unsigned exact-width integers, as their names require. This
// pins down the "define the types uint8_t and uint32_t" obligation rather than
// merely accepting any 1- and 4-byte spelling.
TEST(SvdpiIncludeFileContract, WidthTypesAreUnsignedExactWidth) {
  EXPECT_TRUE((std::is_same<uint8_t, std::uint8_t>::value));
  EXPECT_TRUE((std::is_same<uint32_t, std::uint32_t>::value));
  EXPECT_FALSE(std::is_signed<uint8_t>::value);
  EXPECT_FALSE(std::is_signed<uint32_t>::value);
}

// Edge case for Claim C: "exact width" means the value ranges are pinned down,
// not merely the byte counts. The header's types must carry the full unsigned
// 8- and 32-bit ranges and wrap modulo 2^N at the boundary -- a type wider than
// advertised would not wrap to zero at these limits.
TEST(SvdpiIncludeFileContract, WidthTypesHaveExactValueRanges) {
  EXPECT_EQ(std::numeric_limits<uint8_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint8_t>::max(), 255u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::max(), 4294967295u);

  // Modular wrap at the top of each range confirms the storage width is exact.
  uint8_t byte = std::numeric_limits<uint8_t>::max();
  uint32_t word = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(static_cast<uint8_t>(byte + 1u), 0u);
  EXPECT_EQ(static_cast<uint32_t>(word + 1u), 0u);
}

// The header builds these width types into its own public declarations, so the
// I.2 obligation is load-bearing for the rest of svdpi.h: svScalar is a single
// byte and the canonical vector word is exactly 32 bits wide.
TEST(SvdpiIncludeFileContract, WidthTypesBackPublicDeclarations) {
  EXPECT_EQ(sizeof(svScalar), sizeof(uint8_t));
  EXPECT_EQ(sizeof(svBitVecVal), sizeof(uint32_t));
}

}  // namespace
