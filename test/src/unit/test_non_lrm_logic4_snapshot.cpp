#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

// A Logic4Vec holds a pointer to its words, so a plain copy of one shares them
// with the original. Logic4Snapshot exists so that a baseline held across a
// change does not: these cases mutate the words the capture was taken from,
// which is what DepositBitField does for a packed struct member assignment and
// what the sites writing value.words[i] directly do, and require the captured
// value to be what it was.

TEST(Logic4Snapshot, CaptureSurvivesAnInPlaceWriteToTheSourceWords) {
  Arena arena;
  auto value = MakeLogic4VecVal(arena, 8, 0x10);
  Logic4Snapshot snap;
  snap.Capture(value);
  value.words[0].aval = 0x11;
  EXPECT_EQ(snap.Get().words[0].aval, 0x10u);
}

TEST(Logic4Snapshot, CaptureCarriesTheShapeOfTheValueItWasTakenFrom) {
  Arena arena;
  auto value = MakeLogic4VecVal(arena, 8, 0x10);
  value.is_signed = true;
  Logic4Snapshot snap;
  snap.Capture(value);
  EXPECT_EQ(snap.Get().width, 8u);
  EXPECT_EQ(snap.Get().nwords, value.nwords);
  EXPECT_TRUE(snap.Get().is_signed);
}

TEST(Logic4Snapshot, RecapturingReadsTheValueAsItStandsAtTheSecondCapture) {
  Arena arena;
  auto value = MakeLogic4VecVal(arena, 8, 0x10);
  Logic4Snapshot snap;
  snap.Capture(value);
  value.words[0].aval = 0x22;
  snap.Capture(value);
  EXPECT_EQ(snap.Get().words[0].aval, 0x22u);
}

// A watcher lambda holding a snapshot is copied into the std::function the
// watcher list stores, so a copy that kept pointing at the words the source
// owns would put the aliasing straight back.
TEST(Logic4Snapshot, ACopyOwnsItsWordsRatherThanTheSourceSnapshotWords) {
  Arena arena;
  auto value = MakeLogic4VecVal(arena, 8, 0x10);
  Logic4Snapshot snap;
  snap.Capture(value);
  Logic4Snapshot copy = snap;
  EXPECT_NE(copy.Get().words, snap.Get().words);
  EXPECT_EQ(copy.Get().words[0].aval, 0x10u);
}

TEST(Logic4Snapshot,
     AnAssignedCopyOwnsItsWordsRatherThanTheSourceSnapshotWords) {
  Arena arena;
  auto value = MakeLogic4VecVal(arena, 8, 0x10);
  Logic4Snapshot snap;
  snap.Capture(value);
  Logic4Snapshot copy;
  copy = snap;
  auto other = MakeLogic4VecVal(arena, 8, 0x77);
  snap.Capture(other);
  EXPECT_EQ(copy.Get().words[0].aval, 0x10u);
}

// A vector wider than one word, so that a snapshot copying only the first word
// would differ from one copying all of them.
TEST(Logic4Snapshot, CaptureCopiesEveryWordOfAMultiWordValue) {
  Arena arena;
  auto value = MakeLogic4Vec(arena, 128);
  value.words[0].aval = 0x1234;
  value.words[1].aval = 0x5678;
  Logic4Snapshot snap;
  snap.Capture(value);
  value.words[1].aval = 0x9abc;
  EXPECT_EQ(snap.Get().words[1].aval, 0x5678u);
}

TEST(Logic4Snapshot, ADefaultSnapshotReadsAsAnEmptyValue) {
  Logic4Snapshot snap;
  EXPECT_EQ(snap.Get().nwords, 0u);
}

}  // namespace
