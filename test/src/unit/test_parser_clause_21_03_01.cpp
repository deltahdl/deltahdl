#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, FopenFcloseCall) {
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
