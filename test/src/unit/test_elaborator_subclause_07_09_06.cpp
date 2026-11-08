#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocArrayNextElaboration, NextOnWildcardAssocArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int k;\n"
      "  initial k = aa.next(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'next' shall not be used on the "
                            "wildcard-indexed associative array 'aa'",
                            4, "7.9.6"));
}

TEST(AssocArrayNextElaboration, NextOnIntKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.next(k);\n"
             "endmodule\n"));
}

TEST(AssocArrayNextElaboration, NextOnStringKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.next(s);\n"
             "endmodule\n"));
}

}  // namespace
