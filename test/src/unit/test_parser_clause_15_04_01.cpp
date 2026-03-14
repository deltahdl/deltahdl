#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4.1: new() on an untyped variable parses.
TEST(MailboxNewParser, NewOnUntypedVariable) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §15.4.1: new() with no bound (default 0, unbounded) parses.
TEST(MailboxNewParser, NewUnbounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

// §15.4.1: new(bound) with explicit positive bound parses.
TEST(MailboxNewParser, NewBounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new(10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §15.4.1: Inline declaration with new() parses.
TEST(MailboxNewParser, InlineDeclarationWithNew) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx = new(5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
