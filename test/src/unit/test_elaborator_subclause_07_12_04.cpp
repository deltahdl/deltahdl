#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IteratorIndexWildcard, IndexTypedResultOverWildcardIsRejected) {
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

TEST(IteratorIndexWildcard, UniqueIndexTypedResultOverWildcardIsRejected) {
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
