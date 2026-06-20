#include "fixture_parser.h"

using namespace delta;

namespace {

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

}  // namespace
