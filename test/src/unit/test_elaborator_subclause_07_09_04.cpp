#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.9.4 states of first() "Associative arrays that specify a wildcard index
// type shall not be allowed", so the report names §7.9.4. §7.8.1 bars a
// wildcard array only from a foreach loop and from a §7.12 array manipulation
// method that returns an index, neither of which first() is.
TEST(BuiltinMethodElaboration, FirstOnWildcardAssocArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int k;\n"
      "  initial k = aa.first(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' shall not be used on the "
                            "wildcard-indexed associative array 'aa'",
                            4, "7.9.4"));
}

TEST(BuiltinMethodElaboration, FirstOnIntKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.first(k);\n"
             "endmodule\n"));
}

}  // namespace
