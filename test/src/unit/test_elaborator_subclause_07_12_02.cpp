#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.reverse() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

// §7.12.2: specifying a with clause on shuffle() is a compiler error.
TEST(ArrayOrderingElaboration, ShuffleWithClauseIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.shuffle() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

// §7.12.2: ordering methods reorder fixed or dynamically sized unpacked
// arrays; an associative array is not a legal receiver.
TEST(ArrayOrderingElaboration, SortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, RsortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.rsort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'rsort' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ReverseOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.reverse();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ShuffleOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [int];\n"
      "  initial arr.shuffle();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

}  // namespace
