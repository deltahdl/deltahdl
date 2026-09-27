#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

// No clause of IEEE 1800-2023 describes how deltahdl stores a four-state
// vector, so these cases cover the Logic4Vec helpers in src/common/types.cpp on
// their own terms: comparing two vectors, and depositing one into a window of
// another.

TEST(Logic4Vec, VectorsOfDifferentWidthsAreNotTheSameValue) {
  // Both hold 5 in their only word, so a comparison of the words alone would
  // call them equal. A 4-bit 5 and an 8-bit 5 are not the same value.
  Arena arena;
  auto narrow = MakeLogic4VecVal(arena, 4, 5);
  auto wide = MakeLogic4VecVal(arena, 8, 5);

  EXPECT_FALSE(narrow.SameValueAs(wide));
  EXPECT_TRUE(narrow.SameValueAs(MakeLogic4VecVal(arena, 4, 5)));
}

TEST(Logic4Vec, DepositStopsAtTheTopOfTheDestination) {
  // A four-bit field deposited at bit 6 of an eight-bit vector has two bits
  // that land and two that would stand past its top. The two that land are
  // written, and nothing is written past the vector's width.
  Arena arena;
  auto dst = MakeLogic4VecVal(arena, 8, 0x00);
  auto src = MakeLogic4VecVal(arena, 4, 0xF);

  DepositBitField(dst, 6, src, 4);

  EXPECT_EQ(dst.words[0].aval, 0xC0u);
  EXPECT_EQ(dst.words[0].bval, 0u);
}

TEST(Logic4Vec, DepositPastTheSourceWritesZeros) {
  // A field wider than the value deposited into it takes the value's bits and
  // zeros above them, so the ones already in the destination above the value's
  // width are cleared rather than kept.
  Arena arena;
  auto dst = MakeLogic4VecVal(arena, 8, 0xFF);
  auto src = MakeLogic4VecVal(arena, 2, 0x1);

  DepositBitField(dst, 0, src, 4);

  EXPECT_EQ(dst.words[0].aval, 0xF1u);
  EXPECT_EQ(dst.words[0].bval, 0u);
}

}  // namespace
