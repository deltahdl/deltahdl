#include "fixture_parser.h"

using namespace delta;

namespace {

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
