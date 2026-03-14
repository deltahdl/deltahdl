#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4.8: try_peek() call in initial block elaborates.
TEST(MailboxTryPeekElaborator, TryPeekCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.try_peek(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.8: try_peek() result assigned to variable elaborates.
TEST(MailboxTryPeekElaborator, TryPeekResultAssigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg, status;\n"
      "  initial begin\n"
      "    status = mb.try_peek(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
