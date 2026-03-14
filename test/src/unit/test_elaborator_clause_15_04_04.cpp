#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4.4: try_put() call in initial block elaborates.
TEST(MailboxTryPutElaborator, TryPutCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.try_put(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.4: try_put() result assigned to variable elaborates.
TEST(MailboxTryPutElaborator, TryPutResultAssigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int status;\n"
      "  initial begin\n"
      "    status = mb.try_put(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.4: try_put() with variable argument elaborates.
TEST(MailboxTryPutElaborator, TryPutWithVariableArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int data;\n"
      "  initial begin\n"
      "    mb.try_put(data);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
