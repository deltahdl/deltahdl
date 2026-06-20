#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §21.2.1.7 C1/C3: %s prints ASCII codes as characters, interpreting the
// argument as a sequence of 8-bit codes with each 8 bits forming one character.
// The two bytes 0x48,0x69 render as the characters 'H' and 'i'.
TEST(SysTask, PrintsAsciiCodesAsCharacters) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  uint64_t encoded = (static_cast<uint64_t>('H') << 8) | 'i';
  vals.push_back(MakeLogic4VecVal(arena, 16, encoded));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "Hi");
}

// §21.2.1.7 C2 (shall): for each %s specification a corresponding argument
// follows the string, consumed in order. Two %s specifiers pull two arguments
// left to right.
TEST(SysTask, EachStringSpecifierConsumesItsOwnArgument) {
  Arena arena;
  std::vector<Logic4Vec> vals;
  vals.push_back(MakeLogic4VecVal(arena, 8, 'A'));
  vals.push_back(MakeLogic4VecVal(arena, 8, 'B'));
  auto out = FormatDisplay("%s-%s", vals);
  EXPECT_EQ(out, "A-B");
}

// §21.2.1.7 C5: high-order zero bytes are leading zeros, which are never
// printed, and no termination character is appended. A 24-bit value whose top
// byte is zero yields exactly two characters with nothing before or after them.
TEST(SysTask, LeadingZeroBytesAreNotPrinted) {
  Arena arena;
  std::vector<Logic4Vec> vals;
  uint64_t encoded = (static_cast<uint64_t>('A') << 8) | 'B';  // 0x00_41_42
  vals.push_back(MakeLogic4VecVal(arena, 24, encoded));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "AB");
  EXPECT_EQ(out.size(), 2u);  // no leading null, no trailing terminator
}

// §21.2.1.7 C6: a string-typed argument is accepted, and the character ordering
// runs from the left bound to the right bound. StringToLogic4Vec packs the
// leftmost character at the highest byte, so %s reproduces the original order.
TEST(SysTask, StringTypedArgumentRoundTrips) {
  Arena arena;
  std::vector<Logic4Vec> vals;
  vals.push_back(StringToLogic4Vec(arena, "Verilog"));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "Verilog");
}

// §21.2.1.7 C4 (should): edge case where the value width is not a multiple of
// eight. The value is read right-justified, so the lowest eight bits (0x41)
// form the trailing character 'A' while the leftover upper bits (0x3) form the
// leading character. This is the case that genuinely exercises justification,
// since byte-aligned widths map straight through.
TEST(SysTask, ValueIsRightJustifiedWhenWidthIsNotAByteMultiple) {
  Arena arena;
  std::vector<Logic4Vec> vals;
  vals.push_back(MakeLogic4VecVal(arena, 12, 0x341));
  auto out = FormatDisplay("%s", vals);
  std::string expected;
  expected.push_back(static_cast<char>(0x03));
  expected.push_back('A');
  EXPECT_EQ(out, expected);
  EXPECT_EQ(out.back(), 'A');  // rightmost bits become the last character
}

// §21.2.1.7 C5: boundary of the leading-zero rule -- a value whose every byte
// is zero is entirely leading zeros, so nothing at all is printed.
TEST(SysTask, AllZeroValueProducesEmptyString) {
  Arena arena;
  std::vector<Logic4Vec> vals;
  vals.push_back(MakeLogic4VecVal(arena, 16, 0));
  auto out = FormatDisplay("%s", vals);
  EXPECT_TRUE(out.empty());
}

// §21.2.1.7 C2 (shall): error condition -- a %s with no corresponding argument
// in the list. With the required argument absent, the specifier contributes no
// characters rather than crashing or consuming an out-of-range value.
TEST(SysTask, MissingArgumentLeavesSpecifierEmpty) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%s", vals);
  EXPECT_TRUE(out.empty());
}

}  // namespace
