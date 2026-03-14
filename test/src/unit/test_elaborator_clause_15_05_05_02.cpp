#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.5.2: Event initialized to null elaborates without error.
TEST(NamedEventElaborator, EventInitializedToNull) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev = null;\n"
      "endmodule\n"));
}

// §15.5.5.2: Imperative event = null elaborates without error.
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
