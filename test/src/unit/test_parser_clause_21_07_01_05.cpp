// §21.7.1.5: Limiting size of dump file ($dumplimit)

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumplimitCall) {
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
