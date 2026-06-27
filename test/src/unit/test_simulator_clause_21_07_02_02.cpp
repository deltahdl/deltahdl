#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdValueFormatSim : public VcdTestBase {
 protected:
  // Dump a single signal of the given width at time 0 and return the file
  // contents so a value-change line can be inspected.
  std::string DumpOne(uint32_t width, Logic4Vec value) {
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      auto* var = arena_.Create<Variable>();
      var->value = value;
      vcd.RegisterSignal("sig", width, var);  // ident '!'
      vcd.EndDefinitions();
      vcd.WriteTimestamp(0);
      vcd.DumpAllValues();
    }
    return ReadVcd();
  }
};

// Build a Logic4Vec of the given width from raw aval/bval words so any mix of
// the four logic states can be placed at any bit position: per bit (a,b) =
// (0,0)=0, (1,0)=1, (0,1)=x, (1,1)=z.
Logic4Vec MakeVec(Arena& arena, uint32_t width, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, width, aval);
  v.words[0].bval = bval;
  return v;
}

// C2 (shall): a scalar value change places the value immediately against the
// identifier code with no intervening white space.
TEST_F(VcdValueFormatSim, ScalarChangeHasNoWhitespace) {
  auto content = DumpOne(1, MakeVec(arena_, 1, 0, 0));
  EXPECT_NE(content.find("0!"), std::string::npos);
  // The spaced form a column-aligned writer might produce is forbidden.
  EXPECT_EQ(content.find("0 !"), std::string::npos);
}

// C3 (shall) + C4 + C5/C6 (Table 21-8: 0 and 1 left-extend with 0) + C7
// (Table 21-9 row 1): a 4-bit reg holding 0010 is shortened to b10. The b10
// form simultaneously observes the vector whitespace rule (no space between the
// base letter and the digits, exactly one space before the identifier code) and
// the right-justified retention of the low-order bits after the redundant
// leading zeros are eliminated.
TEST_F(VcdValueFormatSim, ShortensRedundantLeadingZeros) {
  auto content = DumpOne(4, MakeVec(arena_, 4, 0b0010, 0));
  EXPECT_NE(content.find("b10 !"), std::string::npos);
  EXPECT_EQ(content.find("b0010"), std::string::npos);
}

// C6 (Table 21-8: X left-extends with X) + C7 (Table 21-9 row 2): a 4-bit reg
// holding xx10 keeps exactly one leading x, distinguishing the x fill rule from
// the zero fill rule — collapsing both x bits to b10 would misrepresent the
// value.
TEST_F(VcdValueFormatSim, ShortensRedundantLeadingX) {
  // bit3=x, bit2=x, bit1=1, bit0=0 -> aval=0b1110, bval=0b1100 (x=(1,1)).
  auto content = DumpOne(4, MakeVec(arena_, 4, 0b1110, 0b1100));
  EXPECT_NE(content.find("bx10 !"), std::string::npos);
  EXPECT_EQ(content.find("bxx10"), std::string::npos);
}

// C6 (Table 21-8: Z left-extends with Z): an all-z vector collapses to a single
// z, exercising the z fill rule and the guarantee that at least one digit is
// always retained.
TEST_F(VcdValueFormatSim, ShortensRedundantLeadingZ) {
  auto content = DumpOne(4, MakeVec(arena_, 4, 0b0000, 0b1111));  // z=(0,1)
  EXPECT_NE(content.find("bz !"), std::string::npos);
  EXPECT_EQ(content.find("bzz"), std::string::npos);
}

// C5 edge case (Table 21-8: 1 left-extends with 0): because a 1 is
// reconstructed by extending with 0 rather than 1, a high-order 1 can never be
// redundant, so a value composed entirely of ones is already in shortest form
// and no digits are dropped. This exercises the path where the leading-digit
// elimination makes no progress, the complement of every other case here, and
// confirms shortening is not sign-extension.
TEST_F(VcdValueFormatSim, RetainsLeadingOnes) {
  auto content = DumpOne(4, MakeVec(arena_, 4, 0b1111, 0));
  EXPECT_NE(content.find("b1111 !"), std::string::npos);
  // The ones must not be collapsed as if 1 extended with 1.
  EXPECT_EQ(content.find("b1 !"), std::string::npos);
}

// C5/C6 edge case: the shortest-form rule must hold for vectors wider than a
// single machine word. A 70-bit value of 101 spans two storage words (the high
// word is all zeros); after the redundant leading zeros across the word
// boundary are eliminated it must collapse to b101, exercising the multi-word
// digit assembly rather than the single-word fast path the other cases use.
TEST_F(VcdValueFormatSim, ShortensWideVectorSpanningWords) {
  auto content = DumpOne(70, MakeVec(arena_, 70, 0b101, 0));
  EXPECT_NE(content.find("b101 !"), std::string::npos);
  // None of the eliminated high-order zeros from either word may survive.
  EXPECT_EQ(content.find("b0101"), std::string::npos);
}

}  // namespace
}  // namespace delta
