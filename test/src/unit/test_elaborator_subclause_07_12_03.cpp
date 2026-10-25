#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

// §7.12.3: given a with clause, a reduction applies its operation to the with
// expression's values, whatever form the expression takes: a class handle
// member, a string array's element, a real member under a bitwise reduction,
// an unpacked union member, a subarray, a slice, an element's handle member,
// a class handle variable and a whole array have no such operation; an int
// member, a real member under sum, a packed structure member, a union's int
// member, an element of an element, a string's character, a member of an
// element of an array of more dimensions, a member of a variable, a member of
// a call's result, a member of what has no members and a stream's range,
// which stands where the with expression goes (#8053), are left alone.
TEST(BuiltinMethodElaboration, WithExpressionOfAnyFormNeedsTheReduction) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { C h; int a; real r; } s_t;\n"
      "  typedef struct packed { logic [3:0] x; } p_t;\n"
      "  typedef union { int i; real f; } u_t;\n"
      "  typedef struct { u_t u; p_t p; } w_t;\n"
      "  s_t sa[3];\n"
      "  s_t ssa[2][2];\n"
      "  w_t wa[2];\n"
      "  string tags[3];\n"
      "  int m2[2][3];\n"
      "  int ia[2];\n"
      "  C hv;\n"
      "  s_t sv;\n"
      "  int n;\n"
      "  real x;\n"
      "  function s_t mk(); return sv; endfunction\n"
      "  initial begin\n"
      "    n = sa.sum with (item.h);\n"
      "    n = sa.xor with (tags[0]);\n"
      "    n = sa.xor with (item.r);\n"
      "    n = wa.sum with (item.u);\n"
      "    n = sa.sum with (m2[0]);\n"
      "    n = sa.sum with (tags[0:1]);\n"
      "    n = sa.sum with (sa[0].h);\n"
      "    n = sa.sum with (hv);\n"
      "    n = sa.sum with (ia);\n"
      "    n = sa.sum with (item.a);\n"
      "    x = sa.sum with (item.r);\n"
      "    n = wa.xor with (item.p);\n"
      "    n = wa.sum with (item.u.i);\n"
      "    n = sa.sum with (m2[0][1]);\n"
      "    n = sa.sum with (tags[0][0]);\n"
      "    n = sa.sum with (ssa[0][1].a);\n"
      "    n = sa.sum with (ssa[0].a);\n"
      "    n = sa.sum with (sv.a);\n"
      "    n = sa.sum with (mk().a);\n"
      "    n = ia.sum with (item.x);\n"
      "    n = sa.sum with (n.x);\n"
      "    n = sa.sum with (item.zz.a);\n"
      "    n = {>> {ia.sum with [0:1]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "reduces values of a type its operation is not defined for";
  for (uint32_t line = 19; line <= 27; ++line) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "7.12.3"));
  }
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 28 && d.loc.line <= 41 &&
                 d.message.find(kReport) != std::string::npos)
        << d.loc.line << ": " << d.message;
  }
}

}  // namespace
