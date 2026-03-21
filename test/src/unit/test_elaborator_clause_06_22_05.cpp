#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TypeIncompatibleElaboration, StringToIntRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  int i;\n"
      "  initial i = s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
