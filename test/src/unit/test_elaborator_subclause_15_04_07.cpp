#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MailboxPeekElaborator, PeekCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.peek(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.7: peek() copies the message into its argument, which shall be a
// valid left-hand expression.
TEST(MailboxPeekElaborator, PeekIntoAnOperatorExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new;\n"
      "  int a, b;\n"
      "  initial mb.peek(a + b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "message of mailbox method 'peek' is not a valid left-hand expression", 4,
      "15.4.7"));
}

}  // namespace
