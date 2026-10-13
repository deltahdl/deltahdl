#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

// §15.4.8: try_peek() copies the message into its argument, which shall be
// a valid left-hand expression.
TEST(MailboxTryPeekElaborator, TryPeekIntoALiteralIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new;\n"
      "  int ok;\n"
      "  initial ok = mb.try_peek(7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "message of mailbox method 'try_peek' is not a "
                            "valid left-hand expression",
                            4, "15.4.8"));
}

}  // namespace
