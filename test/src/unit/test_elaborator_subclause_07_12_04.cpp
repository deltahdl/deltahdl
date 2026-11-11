#include <gtest/gtest.h>

#include <cstdint>

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

TEST(IteratorIndexWildcard,
     DISABLED_IndexOfAnIteratorOverAWildcardArrayIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int q[$];\n"
      "  int n;\n"
      "  class C;\n"
      "    int w[*];\n"
      "    function int g(); return w.product with (item.index); endfunction\n"
      "  endclass\n"
      "  function automatic int f1(); return aa.sum with (item.index); "
      "endfunction\n"
      "  initial begin\n"
      "    q = aa.find with (item.index == 1);\n"
      "    q = aa.find(x, i) with (x.i > 0);\n"
      "    n = aa.sum with (item.index());\n"
      "    q = aa.find with (item > 1);\n"
      "    n = aa.sum with (item);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "queries the iterator index of a wildcard associative array";
  const uint32_t kLines[] = {7, 9, 11, 12, 13};
  for (uint32_t line : kLines) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, line, "7.12.4"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

TEST(IteratorIndexWildcard, IndexOfAnIteratorOverAKeyedArrayIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int ia[int];\n"
      "  int sa[string];\n"
      "  int ba[byte];\n"
      "  int q[$];\n"
      "  int n;\n"
      "  class C;\n"
      "    int w[int];\n"
      "    function int g(); return w.product with (item.index); endfunction\n"
      "  endclass\n"
      "  function automatic int f1(); return ia.sum with (item.index); "
      "endfunction\n"
      "  initial begin\n"
      "    q = ia.find with (item.index == 1);\n"
      "    q = sa.find(x, i) with (x.i == \"a\");\n"
      "    n = ba.sum with (int'(item.index));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
