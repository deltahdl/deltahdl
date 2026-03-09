#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause05, Cl5_13_ArraySizeMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  int s;\n"
             "  initial s = arr.size();\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_ArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  int s;\n"
             "  initial s = arr.size;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_QueueMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial begin\n"
             "    q.push_back(42);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_QueueSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  int sz;\n"
             "  initial sz = q.size();\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_DynArraySizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size();\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_MutatingMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  initial arr.reverse();\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_13_ReductionMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2] = '{1, 2, 3};\n"
             "  int total;\n"
             "  initial total = arr.sum();\n"
             "endmodule\n"));
}

}
