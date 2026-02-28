// Annex G.4: Mailbox

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex G - Std package: mailbox class (§G.3)
// =============================================================================
TEST_F(AnnexHParseTest, AnnexGMailboxAllMethods) {
  // Mailbox method calls (put, get, peek, try_get, try_peek, try_put, num)
  // as member-access call expressions inside an initial block.
  auto* unit = Parse(
      "module m;\n"
      "  int val;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(val);\n"
      "    mb.peek(val);\n"
      "    val = mb.num();\n"
      "    val = mb.try_get(val);\n"
      "    val = mb.try_peek(val);\n"
      "    val = mb.try_put(99);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
