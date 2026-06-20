#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MailboxPeekParser, PeekCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.peek(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxPeekParser, MultiplePeekCalls) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mb.peek(a);\n"
      "    mb.peek(b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
