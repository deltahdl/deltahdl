#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, ArraySumOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2] = '{1, 2, 3};\n"
             "  int total;\n"
             "  initial total = arr.sum();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArrayProductOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2] = '{2, 3, 5};\n"
             "  int total;\n"
             "  initial total = arr.product();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArrayAndOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:1] = '{8'hFF, 8'h0F};\n"
             "  logic [7:0] r;\n"
             "  initial r = arr.and;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArrayOrOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:1] = '{8'h01, 8'h02};\n"
             "  logic [7:0] r;\n"
             "  initial r = arr.or;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArrayXorOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:1] = '{8'hFF, 8'h0F};\n"
             "  logic [7:0] r;\n"
             "  initial r = arr.xor;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArraySumPropertyAccessOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2] = '{1, 2, 3};\n"
             "  int total;\n"
             "  initial total = arr.sum;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArraySumWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2] = '{1, 2, 3};\n"
             "  int total;\n"
             "  initial total = arr.sum with (item * 2);\n"
             "endmodule\n"));
}

}  // namespace
