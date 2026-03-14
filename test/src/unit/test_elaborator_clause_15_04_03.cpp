#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4.3: put() call in initial block elaborates.
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

// §15.4.3: put() with variable argument elaborates.
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

// §15.4.3: Multiple put() calls elaborate.
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

}  // namespace
