#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
