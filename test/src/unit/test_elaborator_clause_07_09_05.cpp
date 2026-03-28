#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssocArrayLastElaboration, LastOnWildcardAssocArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int k;\n"
      "  initial k = aa.last(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssocArrayLastElaboration, LastOnIntKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.last(k);\n"
             "endmodule\n"));
}

TEST(AssocArrayLastElaboration, LastOnStringKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.last(s);\n"
             "endmodule\n"));
}

}  // namespace
