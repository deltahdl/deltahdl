#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MailboxTryGetElaborator, TryGetCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.try_get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxTryGetElaborator, TryGetResultAssigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg, status;\n"
      "  initial begin\n"
      "    status = mb.try_get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.6: try_get() stores the message into its argument, which shall be a
// valid left-hand expression.
TEST(MailboxTryGetElaborator, TryGetIntoALiteralIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new;\n"
      "  int ok;\n"
      "  initial ok = mb.try_get(5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "message of mailbox method 'try_get' is not a valid left-hand expression",
      4, "15.4.6"));
}

}  // namespace
