#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NamedEventElaborator, EventInitializedToNull) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev = null;\n"
             "endmodule\n"));
}

TEST(NamedEventElaborator, ImperativeEventAssignNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "  initial ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
