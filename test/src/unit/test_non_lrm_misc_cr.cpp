// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection21, MonitorbHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitorb(a);\n"
              "    $monitorh(a);\n"
              "    $monitoro(a);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
