// §15.4.1: New()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
namespace {

// =============================================================================
// §15.4 — Mailbox variable declaration (parsed as named type)
// =============================================================================
TEST(ParserSection15, MailboxVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// LRM section 15.4.1 -- Mailbox new()
// =============================================================================
// §15.4.1: basic mailbox declaration and construction with new().
TEST(ParserSection15, MailboxNewUnbounded) {
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

// §15.4.1: mailbox new() with bounded queue size.
TEST(ParserSection15, MailboxNewBounded) {
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

}  // namespace
