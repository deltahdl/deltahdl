#include <gtest/gtest.h>

#include <cstdint>

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

// §7.12.3: a reduction applies its operation to the elements, or to a with
// expression that is the element: sum and product need the arithmetic
// operators, which a string has not, and the bitwise reductions need bitwise
// operators, which a real has not either. A class handle, an unpacked
// structure, a chandle and an event have neither.
TEST(BuiltinMethodElaboration, ReductionOverAnElementWithoutItsOperation) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { int a; } s_t;\n"
      "  string s[3];\n"
      "  C c[3];\n"
      "  s_t t[3];\n"
      "  real r[3];\n"
      "  chandle h[2];\n"
      "  event ev[2];\n"
      "  int n;\n"
      "  real x;\n"
      "  initial begin\n"
      "    n = s.sum;\n"
      "    n = c.xor;\n"
      "    n = t.and;\n"
      "    n = t.sum with (item);\n"
      "    n = t.sum with (item.a);\n"
      "    n = r.xor;\n"
      "    x = r.sum;\n"
      "    n = h.or;\n"
      "    n = ev.product;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "reduces values of a type its operation is not defined for";
  const uint32_t kLines[] = {13, 14, 15, 16, 18, 20, 21};
  for (uint32_t line : kLines) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "7.12.3"));
  }
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 17u) << d.message;
    EXPECT_NE(d.loc.line, 19u) << d.message;
  }
}

}  // namespace
