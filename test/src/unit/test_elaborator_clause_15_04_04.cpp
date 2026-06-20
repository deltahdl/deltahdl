#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

// §15.4.4: the try_put() message may be any singular expression, explicitly
// including object handles. A class handle passed as the argument elaborates
// without error, just like the integral cases above.
TEST(MailboxTryPutElaborator, TryPutWithObjectHandleArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  mailbox mb;\n"
      "  C obj = new;\n"
      "  initial begin\n"
      "    mb.try_put(obj);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
