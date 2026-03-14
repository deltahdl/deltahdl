#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4.5: get() call in initial block elaborates.
TEST(MailboxGetElaborator, GetCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.5: get() after put() elaborates.
TEST(MailboxGetElaborator, GetAfterPut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.5: Multiple get() calls elaborate.
TEST(MailboxGetElaborator, MultipleGetCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mb.get(a);\n"
      "    mb.get(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
