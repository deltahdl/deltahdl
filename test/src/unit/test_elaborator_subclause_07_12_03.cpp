#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §7.12.3: a with clause may be left off a reduction only where the reduction
// is defined for the array's element type, which for `int m[2][3]` is the
// unpacked `int [3]`, one no operator adds, multiplies or combines bitwise;
// each with-less reduction over it is reported on its line.
TEST(BuiltinMethodElaboration, ReductionOverSubarraysRequiresAWithClause) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int m[2][3];\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = m.sum();\n"
      "    y = m.xor;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array reduction method 'sum' requires a 'with' "
                            "clause over an array whose elements are arrays",
                            5, "7.12.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array reduction method 'xor' requires a 'with' "
                            "clause over an array whose elements are arrays",
                            6, "7.12.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §7.12.3: a reduction over the rows of `int m[2][3]` that reduces each row in
// its with clause is well formed, as is a with-less reduction over a
// one-dimensional array.
TEST(BuiltinMethodElaboration, ReductionOverSubarraysWithAClauseIsOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int m[2][3];\n"
             "  int a[3];\n"
             "  int y;\n"
             "  initial y = m.sum with (item.sum()) + a.sum();\n"
             "endmodule\n"));
}

}  // namespace
