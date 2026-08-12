#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.12.1 — an associative array declared with a wildcard index type ([*]) has
// no concrete index domain, so an index-returning locator (which would have to
// return that index type) is illegal. The rule is applied at elaboration; the
// input is built from the real `int aa[*];` declaration syntax (§7.8.1) and a
// real locator call driven through the elaborator. §7.12.1 states "Associative
// arrays that specify a wildcard index type shall not be allowed" of the index
// locator methods, and §7.8.1 states the same prohibition from the array's
// side -- "Associative arrays that specify a wildcard index type shall not be
// used in a foreach loop (see 12.7.3) or with an array manipulation method
// (see 7.12) that returns an index value or array of values" -- so the report
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
  EXPECT_TRUE(f.has_errors);
  const delta::Diagnostic* diag = FindDiag(
      f, "'find_index' is not allowed on wildcard associative array 'aa'");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.8.1");
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
  EXPECT_TRUE(f.has_errors);
  const delta::Diagnostic* diag = FindDiag(
      f, "'unique_index' is not allowed on wildcard associative array 'aa'");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.8.1");
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

}  // namespace
