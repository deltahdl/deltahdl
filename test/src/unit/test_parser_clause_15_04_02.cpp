#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.2: num() call on a mailbox parses.
TEST(MailboxNumParser, NumCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.num();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.2: num() result assigned to int variable parses.
TEST(MailboxNumParser, NumResultAssigned) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.2: num() used in a conditional expression parses.
TEST(MailboxNumParser, NumInConditional) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    if (mb.num() > 0) begin\n"
      "      $display(\"has messages\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
