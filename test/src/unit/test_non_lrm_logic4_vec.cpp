#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

TEST(Logic4Vec, VectorsOfDifferentWidthsAreNotTheSameValue) {
  Arena arena;
  auto narrow = MakeLogic4VecVal(arena, 4, 5);
  auto wide = MakeLogic4VecVal(arena, 8, 5);

  EXPECT_FALSE(narrow.SameValueAs(wide));
  EXPECT_TRUE(narrow.SameValueAs(MakeLogic4VecVal(arena, 4, 5)));
}

TEST(Logic4Vec, DepositStopsAtTheTopOfTheDestination) {
  Arena arena;
  auto dst = MakeLogic4VecVal(arena, 8, 0x00);
  auto src = MakeLogic4VecVal(arena, 4, 0xF);

  DepositBitField(dst, 6, src, 4);

  EXPECT_EQ(dst.words[0].aval, 0xC0u);
  EXPECT_EQ(dst.words[0].bval, 0u);
}

TEST(Logic4Vec, DepositPastTheSourceWritesZeros) {
  Arena arena;
  auto dst = MakeLogic4VecVal(arena, 8, 0xFF);
  auto src = MakeLogic4VecVal(arena, 2, 0x1);

  DepositBitField(dst, 0, src, 4);

  EXPECT_EQ(dst.words[0].aval, 0xF1u);
  EXPECT_EQ(dst.words[0].bval, 0u);
}

}  // namespace
