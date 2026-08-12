#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
  const delta::Diagnostic* diag =
      FindDiag(f, "'first' is not allowed on wildcard associative array 'aa'");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.9.4");
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
