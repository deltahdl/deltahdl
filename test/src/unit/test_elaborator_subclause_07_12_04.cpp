// Tests for IEEE 1800-2023 clause 7.12.4 -- iterator index querying, negative
// form. The index method returns a value typed as the array's index type: an
// int for ordinary arrays, or the associative index type for an associative
// array. A wildcard-indexed associative array ([*]) has no concrete index
// domain, so it has no type the index method could return; §7.12.4 states such
// arrays shall not be allowed. The prohibition is applied at elaboration: an
// array manipulation method that surfaces the index-typed result (an
// index-returning locator) over a wildcard array is rejected. The input is
// built from the real `int aa[*];` declaration syntax (dependency §7.8/§7.8.1)
// and driven through the elaborator, rather than hand-building the rejection.

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.12.4 -- the index method's return type would have to be the associative
// index type, which a wildcard array leaves undefined; requesting that
// index-typed result over a wildcard array is therefore illegal. §7.12.4's own
// sentence governs the index method of an iterator, which this source does not
// call; what it does call is an index-returning array manipulation method,
// which §7.8.1 bars from a wildcard associative array, so the report names
// §7.8.1.
TEST(IteratorIndexWildcard, IndexTypedResultOverWildcardIsRejected) {
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

// §7.12.4 -- the same prohibition reached through the unique family:
// unique_index also yields the index-typed result, so it too is rejected over a
// wildcard associative array. A separate input form of the same negative rule.
// The report names §7.8.1 for the reason given above
// IndexTypedResultOverWildcardIsRejected.
TEST(IteratorIndexWildcard, UniqueIndexTypedResultOverWildcardIsRejected) {
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

// §7.12.4 -- boundary of the negative rule: an integral-indexed associative
// array (§7.8) has a concrete index type, so surfacing the index-typed result
// is allowed and elaborates cleanly. This fixes the wildcard case as the sole
// rejection.
TEST(IteratorIndexWildcard, IndexTypedResultOverIntegralKeyIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[int];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
