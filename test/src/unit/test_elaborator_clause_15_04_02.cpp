#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4.2: num() call in initial block elaborates.
TEST(MailboxNumElaborator, NumCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.2: num() result assigned to int elaborates.
TEST(MailboxNumElaborator, NumResultAssigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
