#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, AnnexGRandomizeCall) {

  auto* unit = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = $urandom;\n"
      "    x = $urandom();\n"
      "    x = $urandom_range(0, 100);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}
