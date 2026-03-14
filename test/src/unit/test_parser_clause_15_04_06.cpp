#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.6: try_get() call with ref argument parses.
TEST(MailboxTryGetParser, TryGetCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.try_get(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.6: try_get() result assigned to variable parses (returns int).
TEST(MailboxTryGetParser, TryGetResultAssigned) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg, status;\n"
      "  initial begin\n"
      "    status = mb.try_get(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.6: try_get() used in conditional parses.
TEST(MailboxTryGetParser, TryGetInConditional) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    if (mb.try_get(msg)) begin\n"
      "      $display(\"got message\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
