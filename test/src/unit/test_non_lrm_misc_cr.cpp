// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection21, StrobeBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $strobe(\"val=%d\", x);\n"
              "endmodule\n"));
}

TEST(ParserSection21, StrobebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $strobeb(a);\n"
              "    $strobeh(a);\n"
              "    $strobeo(a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, MonitorBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $monitor(\"a=%b b=%b\", a, b);\n"
              "endmodule\n"));
}

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
