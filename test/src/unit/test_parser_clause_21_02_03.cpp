// §21.2.3: Continuous monitoring

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, MonitorOnOff) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitoron;\n"
              "    $monitoroff;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
