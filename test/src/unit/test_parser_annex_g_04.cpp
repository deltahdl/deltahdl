#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, AnnexGMailboxAllMethods) {
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
