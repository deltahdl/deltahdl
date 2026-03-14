#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.5: get() call with ref argument parses.
TEST(MailboxGetParser, GetCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.5: get() on a declared mailbox with new parses.
TEST(MailboxGetParser, GetAfterNew) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb = new();\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.5: Multiple get() calls in sequence parse.
TEST(MailboxGetParser, MultipleGetCalls) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mb.get(a);\n"
      "    mb.get(b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
