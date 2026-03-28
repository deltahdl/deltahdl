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

}  // namespace
