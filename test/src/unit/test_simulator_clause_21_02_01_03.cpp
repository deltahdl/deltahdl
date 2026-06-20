#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Build a 4-state vector from an MSB-first string of 0/1/x/z characters, so a
// test reads in the same bit order the LRM writes its literals. The encoding
// matches Logic4Vec::ToString: x is (aval 0, bval 1) and z is (aval 1, bval 1).
Logic4Vec MakeVec(Arena& arena, const std::string& bits) {
  auto v = MakeLogic4Vec(arena, static_cast<uint32_t>(bits.size()));
  for (size_t k = 0; k < bits.size(); ++k) {
    auto idx = static_cast<uint32_t>(bits.size() - 1 - k);
    uint64_t mask = uint64_t{1} << (idx % 64);
    Logic4Word& w = v.words[idx / 64];
    switch (bits[k]) {
      case '1':
        w.aval |= mask;
        break;
      case 'x':
        w.bval |= mask;
        break;
      case 'z':
        w.aval |= mask;
        w.bval |= mask;
        break;
      default:
        break;  // '0' leaves the bit clear
    }
  }
  return v;
}

// §21.2.1.3 (D1): a decimal value whose bits are all unknown shows a single
// lowercase x.
TEST(UnknownAndHighImpedance, DecimalAllUnknownIsLowercaseX) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "xxxx"), 'd'), "x");
}

// §21.2.1.3 (D2): a decimal value whose bits are all high-impedance shows a
// single lowercase z.
TEST(UnknownAndHighImpedance, DecimalAllHighZIsLowercaseZ) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "zzzz"), 'd'), "z");
}

// §21.2.1.3 (D3): with some but not all bits unknown, decimal shows uppercase
// X.
TEST(UnknownAndHighImpedance, DecimalSomeUnknownIsUppercaseX) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "01x0"), 'd'), "X");
}

// §21.2.1.3 (D4): with some but not all bits high-impedance and none unknown,
// decimal shows uppercase Z.
TEST(UnknownAndHighImpedance, DecimalSomeHighZIsUppercaseZ) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "01z0"), 'd'), "Z");
}

// §21.2.1.3 (D4 exception): high-impedance bits accompanied by any unknown bit
// fall back to uppercase X rather than Z.
TEST(UnknownAndHighImpedance, DecimalMixedHighZAndUnknownIsUppercaseX) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "xz01"), 'd'), "X");
}

// §21.2.1.3 (D5): a decimal status character is right-justified within a
// fixed-width field. Padding a one-bit unknown value into a five-column field
// puts the x at the right edge. (LRM example: $display("%d", 1'bx).)
TEST(UnknownAndHighImpedance, DecimalStatusCharRightJustifiedInField) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeVec(arena, "x")};
  EXPECT_EQ(FormatDisplay("%5d", vals), "    x");
}

// §21.2.1.3 (H1/H2/H4): the LRM's worked hex example. A 14-bit value extended
// with leading x's groups into four hex digits: two all-x groups (lowercase x),
// one partly-unknown group (uppercase X), and one known group (a).
TEST(UnknownAndHighImpedance, HexExampleFromLrm) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "xxxxxxxxx01010"), 'h'), "xxXa");
}

// §21.2.1.3 (H1/H2/H4): the LRM's worked octal example, grouping three bits per
// digit: a known 1, an all-x group, a known 5, and a partly-unknown group.
TEST(UnknownAndHighImpedance, OctalExampleFromLrm) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "001xxx101x01"), 'o'), "1x5X");
}

// §21.2.1.3 (H3): a hex group that is entirely high-impedance shows a lowercase
// z for that digit.
TEST(UnknownAndHighImpedance, HexAllHighZGroupIsLowercaseZ) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "zzzz"), 'h'), "z");
}

// §21.2.1.3 (H5): a hex group with some but not all bits high-impedance and no
// unknown bits shows uppercase Z.
TEST(UnknownAndHighImpedance, HexSomeHighZGroupIsUppercaseZ) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "01z1"), 'h'), "Z");
}

// §21.2.1.3 (H5 exception): a hex group mixing high-impedance and unknown bits
// shows uppercase X.
TEST(UnknownAndHighImpedance, HexMixedHighZAndUnknownGroupIsUppercaseX) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "x1z1"), 'h'), "X");
}

// §21.2.1.3 (B1): binary prints every bit separately using 0, 1, x, and z.
TEST(UnknownAndHighImpedance, BinaryPrintsEachBitWithXAndZ) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "1x0z"), 'b'), "1x0z");
}

// §21.2.1.3 boundary: the status-character rules apply only when unknown or
// high-impedance bits are present. A fully known decimal value keeps its plain
// numeral and never picks up an x/z status character.
TEST(UnknownAndHighImpedance, DecimalKnownValueShowsNumeral) {
  Arena arena;
  EXPECT_EQ(FormatArg(MakeVec(arena, "1010"), 'd'), "10");
}

// §21.2.1.3 (H2/H4) edge: the grouping rules hold for values wider than one
// machine word. Here a 68-bit value carries a lone unknown bit in its top hex
// group (some but not all unknown -> uppercase X) while the rest is known.
TEST(UnknownAndHighImpedance, HexUnknownBitInUpperWord) {
  Arena arena;
  std::string bits(68, '0');
  bits[0] = 'x';   // most significant bit -> sits in the top hex group
  bits[64] = '1';  // contributes to the least significant hex digit
  bits[66] = '1';
  EXPECT_EQ(FormatArg(MakeVec(arena, bits), 'h'),
            "X" + std::string(15, '0') + "a");
}

// §21.2.1.3 edge: an explicit field width (the §21.2.1.2 feature) must not
// collapse a value down through its integer bits, which would discard the x/z
// information. A single high-impedance hex group keeps its uppercase Z status
// character and is then padded to the requested width.
TEST(UnknownAndHighImpedance, HexStatusCharSurvivesFieldWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeVec(arena, "01z1")};
  EXPECT_EQ(FormatDisplay("%2h", vals), "0Z");
}

}  // namespace
