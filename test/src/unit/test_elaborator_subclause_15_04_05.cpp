#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

// §15.4.5: get() stores the message into its argument, which shall be a
// valid left-hand expression.
TEST(MailboxGetElaborator, GetIntoAnOperatorExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mb.put(5);\n"
      "    mb.get(a + b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "message of mailbox method 'get' is not a valid left-hand expression", 6,
      "15.4.5"));
}

// §15.4.5: the message get() retrieves into is singular, which a variable
// of an unpacked structure type is not (§6.4).
TEST(MailboxGetElaborator, GetIntoAnUnpackedStructIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int x; real y; } s_t;\n"
      "  mailbox mb = new;\n"
      "  s_t s;\n"
      "  initial mb.get(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "message of mailbox method 'get' is of an unpacked aggregate type", 5,
      "15.4.5"));
}

// §15.4.5: a variable, a select, a member and a concatenation of variables
// are valid left-hand expressions to retrieve into.
TEST(MailboxGetElaborator,
     GetIntoAVariableSelectMemberOrConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C; int x; endclass\n"
      "  mailbox mb = new;\n"
      "  int v, arr[2];\n"
      "  bit [3:0] a, b;\n"
      "  C h = new;\n"
      "  initial begin\n"
      "    mb.get(v);\n"
      "    mb.get(arr[0]);\n"
      "    mb.get(h.x);\n"
      "    mb.get({a, b});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
