#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MailboxPutElaborator, PutCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxPutElaborator, PutWithVariableArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int val;\n"
      "  initial begin\n"
      "    mb.put(val);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxPutElaborator, MultiplePutCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.put(1);\n"
      "    mb.put(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
