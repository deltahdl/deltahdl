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

// §15.4.3: the put() message may be any singular expression, and object
// handles are explicitly admissible. A class-handle expression is therefore a
// valid argument; the elaborator must accept it without error, exactly as it
// does for an integer expression.
TEST(MailboxPutElaborator, PutWithObjectHandleArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  mailbox mb;\n"
      "  C obj = new;\n"
      "  initial begin\n"
      "    mb.put(obj);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
