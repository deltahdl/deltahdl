#include <gtest/gtest.h>

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.12.1 — an associative array declared with a wildcard index type ([*]) has
// no concrete index domain, so an index-returning locator (which would have to
// return that index type) is illegal. The rule is applied at elaboration; the
// input is built from the real `int aa[*];` declaration syntax (§7.8.1) and a
// real locator call driven through the elaborator. §7.12.1 bars the index
// locator methods from an associative array with a wildcard index type, and
// §7.8.1 states the same prohibition from the array's side -- such an array may
// not be used in a foreach loop (§12.7.3) or with an array manipulation method
// (§7.12) that returns an index value or an array of values -- so the report
// names §7.8.1.
TEST(ArrayLocatorWildcard, FindIndexOnWildcardIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'find_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.12.1 — unique_index also yields an array of index values, so it too is
// rejected on a wildcard associative array. It reaches the prohibition through
// a distinct locator (the unique family rather than the find family), a
// separate input form of the same rule. The report names §7.8.1 for the reason
// given above FindIndexOnWildcardIsRejected.
TEST(ArrayLocatorWildcard, UniqueIndexOnWildcardIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.unique_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'unique_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.12.1 — the wildcard prohibition is specific to the index-returning
// locators: an element locator (find) returns element values, not indices, so
// applying it to a wildcard associative array is allowed and elaborates
// cleanly. This contrast fixes the boundary of the rule's negative form.
TEST(ArrayLocatorWildcard, ElementFindOnWildcardIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int found[$];\n"
      "  initial found = aa.find with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.12.1 and §7.12.2: min, max, unique, unique_index, sort and rsort compare
// the elements by their relational operators unless a with clause gives what
// to compare, and then compare that. A class handle and an unpacked structure
// have no relational operators, so the element itself, or a with expression
// that is the element, is not something they can compare. An enumeration has
// them, and so does a member of int or a variable named in the with clause.
TEST(ArrayLocatorValidation, ComparingValuesWithoutRelationalOperators) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { int a; } s_t;\n"
      "  typedef enum {A, B} e_t;\n"
      "  C ca[3];\n"
      "  s_t sa[3];\n"
      "  C cq[$];\n"
      "  s_t sq[$];\n"
      "  e_t ea[2];\n"
      "  e_t ea2[2];\n"
      "  int k;\n"
      "  initial begin\n"
      "    ca.sort;\n"
      "    sq = sa.min;\n"
      "    cq = ca.unique;\n"
      "    sa.rsort with (item);\n"
      "    sa.sort with (item.a);\n"
      "    sa.sort(x) with (x);\n"
      "    ca.sort with (k);\n"
      "    sq = sa.max(y) with (y.a);\n"
      "    ea.sort;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'sort' compares values of a type "
                            "without relational operators",
                            13, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'min' compares values of a type "
                            "without relational operators",
                            14, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'unique' compares values of a type "
                            "without relational operators",
                            15, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'rsort' compares values of a type "
                            "without relational operators",
                            16, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags,
                            "array method 'sort' compares values of a type "
                            "without relational operators",
                            18, "7.12.2"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 17u) << d.message;
    EXPECT_FALSE(d.loc.line >= 19 && d.loc.line <= 21)
        << d.loc.line << ": " << d.message;
  }
}

// §7.12.1 and §7.12.2: given a with clause, a method compares the with
// expression's values, so their type needs the relational operators whatever
// form the expression takes: a class handle member, a member that is an
// unpacked array and a member of a member that is a handle have none; an int
// member, a member of a class element, a member no element has, a class
// handle variable's member and an element of a member array do.
TEST(BuiltinMethodElaboration,
     WithExpressionOfAnyFormNeedsRelationalOperators) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class C; int v; endclass\n"
      "  typedef struct { C h; int a; int arr[2]; } s_t;\n"
      "  typedef struct { s_t inner; } o_t;\n"
      "  s_t sa[3];\n"
      "  s_t sq[$];\n"
      "  o_t oa[2];\n"
      "  o_t oq[$];\n"
      "  C ca[3];\n"
      "  C cq[$];\n"
      "  C hv;\n"
      "  initial begin\n"
      "    sq = sa.min with (item.h);\n"
      "    sa.sort with (item.arr);\n"
      "    oq = oa.min with (item.inner.h);\n"
      "    sq = sa.max with (item.a);\n"
      "    oq = oa.min with (item.inner.a);\n"
      "    cq = ca.min with (item.v);\n"
      "    sq = sa.unique with (item.zz);\n"
      "    cq = ca.max with (hv.v);\n"
      "    sq = sa.min with (item.arr[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "compares values of a type without relational operators";
  EXPECT_TRUE(ReportedError(diags, kReport, 13, "7.12.1"));
  EXPECT_TRUE(ReportedError(diags, kReport, 14, "7.12.2"));
  EXPECT_TRUE(ReportedError(diags, kReport, 15, "7.12.1"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 16 && d.loc.line <= 21 &&
                 d.message.find(kReport) != std::string::npos)
        << d.loc.line << ": " << d.message;
  }
}

}  // namespace
