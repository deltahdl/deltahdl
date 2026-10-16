#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.5, §7.9, §7.10.2 and §7.12: an array has §7.12's manipulation methods and
// the methods its kind lists, and no others. A member select written on an
// array as though it held a handle names no method either.
TEST(ArrayMethodValidation, NameNoMethodOfTheArraysKindIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int fx[3];\n"
      "  int dy[];\n"
      "  int aa[string];\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial begin\n"
      "    q.foo();\n"
      "    dy.push_back(1);\n"
      "    aa.pop_front();\n"
      "    n = fx.size();\n"
      "    q.h.run();\n"
      "    q.push_back(1);\n"
      "    dy.delete();\n"
      "    n = aa.exists(\"a\");\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the queue 'q'", 8, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'push_back' is not a built-in method of the dynamic array 'dy'",
      9, "7.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'pop_front' is not a built-in method of the associative array 'aa'", 10,
      "7.9"));
  EXPECT_TRUE(ReportedError(
      diags, "'size' is not a built-in method of the fixed-size array 'fx'", 11,
      "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the queue 'q'", 12, "7.10.2"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 13 && d.loc.line <= 15)
        << d.loc.line << ": " << d.message;
  }
}

// The same of an array reached through members: a structure's member, s.q,
// and a property of the class a variable holds a handle of, h.q. The methods
// of each kind are still accepted there, and so is §18.8's rand_mode on an
// array property declared rand, which gives it no other method. A structure
// variable is no object, so a member declared rand gains no rand_mode.
TEST(ArrayMethodValidation, AMemberArraysNameOfNoMethodIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int q[$]; int fx[2]; rand int ra[2]; } s_t;\n"
      "  class C; int q[$]; int aa[string]; rand int ra[2]; endclass\n"
      "  s_t s; C h = new; int n;\n"
      "  initial begin\n"
      "    s.q.foo();\n"
      "    h.q.bar();\n"
      "    s.fx.delete();\n"
      "    h.aa.pop_front();\n"
      "    h.ra.baz();\n"
      "    s.ra.rand_mode(0);\n"
      "    s.q.delete();\n"
      "    n = h.q.size();\n"
      "    n = h.aa.num();\n"
      "    s.fx.sort();\n"
      "    h.ra.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the queue 's.q'", 6, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the queue 'h.q'", 7, "7.10.2"));
  EXPECT_TRUE(ReportedError(
      diags, "'delete' is not a built-in method of the fixed-size array 's.fx'",
      8, "7.12"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'pop_front' is not a built-in method of the associative array 'h.aa'", 9,
      "7.9"));
  EXPECT_TRUE(ReportedError(
      diags, "'baz' is not a built-in method of the fixed-size array 'h.ra'",
      10, "7.12"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'rand_mode' is not a built-in method of the fixed-size array 's.ra'", 11,
      "7.12"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 12 && d.loc.line <= 16)
        << d.loc.line << ": " << d.message;
  }
}

// §7.8: a member whose index type is a name the scope declares, a typedef or a
// class, is an associative array, and takes that kind's methods, num among
// them, which no fixed-size array has.
TEST(ArrayMethodValidation, AMembersNamedIndexTypeMakesItAssociative) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef int idx_t;\n"
      "  class K; endclass\n"
      "  class C; int bt[idx_t]; int bk[K]; endclass\n"
      "  C h = new; int n;\n"
      "  initial begin\n"
      "    n = h.bt.num();\n"
      "    n = h.bk.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_FALSE(d.loc.line >= 7 && d.loc.line <= 8)
        << d.loc.line << ": " << d.message;
  }
}

// What that rule passes over: a receiver it cannot trace to one member of a
// variable -- a member of a member, a package's array, an element of an
// array, an instance's array -- and a member that is no array, each written
// with a method of its own kind, so nothing is reported.
TEST(ArrayMethodValidation, ReceiversNotOneMemberOfAVariablePassClean) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int q[$]; endpackage\n"
      "module child; int q[$]; endmodule\n"
      "module top;\n"
      "  typedef struct { int q[$]; } in_t;\n"
      "  typedef struct { in_t in; string str; } out_t;\n"
      "  out_t ss; int ar[2][$]; int n;\n"
      "  child u();\n"
      "  initial begin\n"
      "    ss.in.q.delete();\n"
      "    p::q.delete();\n"
      "    ar[0].delete();\n"
      "    u.q.delete();\n"
      "    n = ss.str.len();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_FALSE(d.loc.line >= 9 && d.loc.line <= 13)
        << d.loc.line << ": " << d.message;
  }
}

// §7.12, §7.12.1 and §7.12.5: an iterator argument without a with clause, a
// find locator without one and map without one are each reported as the
// design is elaborated, whether or not the call ever runs.
TEST(ArrayMethodValidation, MissingWithClauseReportedAtElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int r[$];\n"
      "  bit go = 0;\n"
      "  initial if (go) begin\n"
      "    r = q.find(x);\n"
      "    r = q.find_index;\n"
      "    r = q.map();\n"
      "    q.sort(x);\n"
      "    r = q.find with (item > 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 6,
                            "7.12"));
  EXPECT_TRUE(ReportedError(
      diags, "array locator method 'find_index' requires a 'with' clause", 7,
      "7.12.1"));
  EXPECT_TRUE(ReportedError(
      diags, "array method 'map' requires a 'with' clause", 8, "7.12.5"));
  EXPECT_TRUE(ReportedError(diags, "iterator argument without 'with' clause", 9,
                            "7.12"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 10u) << d.message;
}

}  // namespace
