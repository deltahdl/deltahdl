#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.4: mailbox bare declaration parses.
TEST(MailboxParser, BareDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbxRcv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.4: multiple mailbox declarations in one module.
TEST(MailboxParser, MultipleMailboxDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb1;\n"
      "  mailbox mb2;\n"
      "  mailbox mb3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.4: mailbox is recognized as a type without a class declaration.
TEST(MailboxParser, NoClassDeclarationRequired) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4: mailbox declaration with new() constructor parses.
TEST(MailboxParser, DeclarationWithNew) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb = new();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4: mailbox with method calls in procedural context.
TEST(MailboxParser, MethodCallsInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
