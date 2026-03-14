#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.5: Event declaration with initializer from another event elaborates.
TEST(EventOperationsElaborator, EventInitializerFromAnotherEvent) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n"));
}

// §15.5.5: Imperative event-to-event assignment elaborates without error.
TEST(EventOperationsElaborator, ImperativeEventAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event a, b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §15.5.5: Multiple event variables can be assigned in sequence.
TEST(EventOperationsElaborator, ChainedEventAssignment) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b, c;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    b = c;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
