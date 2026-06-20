#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DisplayWithFormatSpecifiers) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] a;\n"
              "  initial begin\n"
              "    a = 8'hFF;\n"
              "    $display(\"dec=%0d hex=%0h bin=%0b oct=%0o\", a, a, a, a);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
