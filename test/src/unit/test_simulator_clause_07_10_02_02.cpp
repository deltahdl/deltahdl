#include "fixture_simulator.h"

using namespace delta;

namespace {

// §7.10.2.2's insert() rules operate on a queue whose contents come from a
// declaration + initializer (§7.10) and on an index taken from a variable of
// the prototype's `integer` formal, so the behavior depends on how those inputs
// are produced. Each test builds both from real source and drives them through
// the full pipeline (parse, elaborate, lower, run), observing the production
// insert() path (QueueInsertAt reached via TryEvalQueueMethodCall) apply each
// rule.

// Claim: insert(index, item) places item at the ordinal index position,
// shifting the trailing elements up by one.
TEST(QueueMethods, InsertAtIndexFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 30};\n"
      "  initial q.insert(1, 20);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim: index 0 inserts at the front of the queue.
TEST(QueueMethods, InsertAtFrontFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{20, 30};\n"
      "  initial q.insert(0, 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim: an index equal to the current size is in range and appends the item at
// the end (only indices strictly greater than the size are rejected).
TEST(QueueMethods, InsertAtEndFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(2, 30);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim: inserting at index 0 into an empty queue (the queue is empty when no
// initializer is given, per §7.10) yields a single-element queue.
TEST(QueueMethods, InsertIntoEmptyQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$];\n"
      "  initial q.insert(0, 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

// Claim (error path): an index greater than the current size leaves the queue
// unchanged.
TEST(QueueMethods, InsertOutOfRangeIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(100, 99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// Claim (error path): the smallest index that exceeds the current size (size+1)
// is the exact off-by-one edge of the range guard and must leave the queue
// unchanged, complementing the in-range append at index == size above.
TEST(QueueMethods, InsertJustPastEndIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(3, 99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// Claim (error path): a negative index leaves the queue unchanged. The index is
// held in an `integer` variable, matching the prototype's signed 4-state
// formal.
TEST(QueueMethods, InsertNegativeIndexIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = -1;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// Claim (error path): an index carrying x/z bits leaves the queue unchanged.
// The prototype's index formal is `integer` (4-state) precisely so an unknown
// value survives to the insert() call and can be detected.
TEST(QueueMethods, InsertXzIndexIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = 'x;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// Element-type input form: insert() is defined for a queue of any element type
// (item is `element_t`), not just int. Insert into a queue of packed 4-state
// vectors and confirm the item lands at the index with neighbors in order.
TEST(QueueMethods, InsertOnVectorQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$] = '{8'hAA, 8'hCC};\n"
      "  initial q.insert(1, 8'hBB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0xAAu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xBBu);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xCCu);
}

// Item-value input form: "inserts the given item" must store the item
// faithfully even when it carries unknown bits. Inserting an item with x/z bits
// into a 4-state queue keeps those unknown bits in the stored element (the
// known bits still read back), distinct from every case above where the item is
// fully determined.
TEST(QueueMethods, InsertPreservesUnknownItemBitsFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$] = '{8'h11};\n"
      "  initial q.insert(0, 8'b1010_xxxx);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  // The inserted element is not fully known: its low nibble carries x bits.
  EXPECT_FALSE(q->elements[0].IsKnown());
  // The originally-present element is undisturbed and still fully known.
  EXPECT_TRUE(q->elements[1].IsKnown());
  EXPECT_EQ(q->elements[1].ToUint64(), 0x11u);
}

// Error-path input form: the rule rejects an index with x OR z bits. The x case
// is covered above; this exercises the z variant. The index is held in an
// `integer` (4-state) variable so the z value survives to the insert() call,
// which must leave the queue unchanged.
TEST(QueueMethods, InsertWithZIndexIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = 'z;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

}  // namespace
