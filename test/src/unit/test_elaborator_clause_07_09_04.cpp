#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
