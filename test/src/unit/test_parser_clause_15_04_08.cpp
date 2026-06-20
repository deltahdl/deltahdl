#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MailboxTryPeekParser, TryPeekCallParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.try_peek(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxTryPeekParser, TryPeekResultAssigned) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg, status;\n"
      "  initial begin\n"
      "    status = mb.try_peek(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxTryPeekParser, TryPeekInConditional) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    if (mb.try_peek(msg)) begin\n"
      "      $display(\"has message\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
