#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.9.7 states of prev() "Associative arrays that specify a wildcard index
// type shall not be allowed", so the report names §7.9.7. §7.8.1 bars a
// wildcard array only from a foreach loop and from a §7.12 array manipulation
// method that returns an index, neither of which prev() is.
TEST(AssocArrayPrevElaboration, PrevOnWildcardAssocArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int k;\n"
      "  initial k = aa.prev(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
  const delta::Diagnostic* diag =
      FindDiag(f,
               "traversal method 'prev' shall not be used on the "
               "wildcard-indexed associative array 'aa'");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.9.7");
}

TEST(AssocArrayPrevElaboration, PrevOnIntKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.prev(k);\n"
             "endmodule\n"));
}

TEST(AssocArrayPrevElaboration, PrevOnStringKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.prev(s);\n"
             "endmodule\n"));
}

}  // namespace
