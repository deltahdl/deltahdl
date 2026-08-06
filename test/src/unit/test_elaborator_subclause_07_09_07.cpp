#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
