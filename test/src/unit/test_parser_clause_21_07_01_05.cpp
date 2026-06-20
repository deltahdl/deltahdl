#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumplimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpfile(\"out.vcd\");\n"
              "    $dumplimit(1000000);\n"
              "    $dumpvars;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
