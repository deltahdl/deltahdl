// §21.3.1: for the functional description of $fopen.

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FopenFcloseCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"output.log\", \"w\");\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
