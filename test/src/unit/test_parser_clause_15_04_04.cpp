#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.4: try_put() call on a mailbox parses.
TEST(MailboxTryPutParser, TryPutCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.try_put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.4: try_put() result assigned to variable parses (returns int).
TEST(MailboxTryPutParser, TryPutResultAssigned) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int status;\n"
      "  initial begin\n"
      "    status = mb.try_put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.4: try_put() used in conditional parses.
TEST(MailboxTryPutParser, TryPutInConditional) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    if (mb.try_put(42)) begin\n"
      "      $display(\"placed\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.4: try_put() with variable expression parses.
TEST(MailboxTryPutParser, TryPutWithVariableExpression) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int data;\n"
      "  initial begin\n"
      "    mb.try_put(data);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
