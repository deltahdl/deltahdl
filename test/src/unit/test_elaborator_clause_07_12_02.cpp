#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ArrayOrderingElaboration, ArrayReverseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  initial arr.reverse();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArraySortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayRsortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayShuffleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.shuffle();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, SortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort with (item);\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, RsortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort with (item);\n"
             "endmodule\n"));
}

// §7.12.2: ordering methods apply to a dynamically sized array, not just a
// fixed one. The validator must recognize a dynamic array as a legal (non-
// associative) receiver and accept it, unlike the associative case below.
TEST(ArrayOrderingElaboration, SortOnDynamicArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a [] = '{3, 1, 2};\n"
             "  initial a.sort();\n"
             "endmodule\n"));
}

// §7.12.2: a queue is the other dynamically sized array form; it too is a legal
// ordering-method receiver and must elaborate without error.
TEST(ArrayOrderingElaboration, SortOnQueueOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$] = '{3, 1, 2};\n"
             "  initial q.sort;\n"
             "endmodule\n"));
}

// §7.12.2: specifying a with clause on reverse() is a compiler error.
TEST(ArrayOrderingElaboration, ReverseWithClauseIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.reverse() with (item);\n"
             "endmodule\n"));
}

// §7.12.2: specifying a with clause on shuffle() is a compiler error.
TEST(ArrayOrderingElaboration, ShuffleWithClauseIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.shuffle() with (item);\n"
             "endmodule\n"));
}

// §7.12.2: ordering methods reorder fixed or dynamically sized unpacked
// arrays; an associative array is not a legal receiver.
TEST(ArrayOrderingElaboration, SortOnAssocArrayIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [string];\n"
             "  initial arr.sort();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, RsortOnAssocArrayIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [string];\n"
             "  initial arr.rsort();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ReverseOnAssocArrayIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [string];\n"
             "  initial arr.reverse();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ShuffleOnAssocArrayIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int arr [int];\n"
             "  initial arr.shuffle();\n"
             "endmodule\n"));
}

}  // namespace
