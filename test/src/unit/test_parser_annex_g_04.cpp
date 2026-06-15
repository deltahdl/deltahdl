// IEEE 1800-2023 Annex G.4 (Std package -- Mailbox).
//
// The std-package `mailbox` prototype (G.4) introduces `mailbox` as a built-in
// parameterized class type. These tests observe the parser recognizing that
// std-package type name (Parser::known_types_ seeds "mailbox") so that
// declarations and the prototype's method calls parse without any user
// `class mailbox` definition. The prototype's semantics belong to clause 15.4.

#include "fixture_parser.h"

using namespace delta;

namespace {

// `mailbox` is a known std-package type name on its own.
TEST(MailboxStdPackageParser, BareDeclarationOfBuiltInType) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The full prototype call surface parses: new / put / try_put / get / try_get /
// peek / try_peek, with the documented default new() argument omitted.
TEST(MailboxStdPackageParser, PrototypeMethodsParse) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx = new();\n"
      "  int msg;\n"
      "  int got;\n"
      "  initial begin\n"
      "    mbx.put(msg);\n"
      "    got = mbx.try_put(msg);\n"
      "    mbx.get(msg);\n"
      "    got = mbx.try_get(msg);\n"
      "    mbx.peek(msg);\n"
      "    got = mbx.try_peek(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The prototype declares num() and try_get() as `function int`, so their result
// is a value and must parse in an expression position such as an if-condition.
TEST(MailboxStdPackageParser, ValueReturningMethodsUsableInExpression) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx = new();\n"
      "  int msg;\n"
      "  initial begin\n"
      "    if (mbx.num() == 0) mbx.put(msg);\n"
      "    if (mbx.try_get(msg)) mbx.put(msg);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
