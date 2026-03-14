#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.3: put() call on a mailbox parses.
TEST(MailboxPutParser, PutCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.3: put() with a variable expression parses.
TEST(MailboxPutParser, PutWithVariableExpression) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  int data;\n"
      "  initial begin\n"
      "    mbx.put(data);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.3: put() on parameterized mailbox parses.
TEST(MailboxPutParser, PutOnParameterizedMailbox) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "    mbx.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.3: Multiple put() calls in sequence parse.
TEST(MailboxPutParser, MultiplePutCalls) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx.put(1);\n"
      "    mbx.put(2);\n"
      "    mbx.put(3);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
