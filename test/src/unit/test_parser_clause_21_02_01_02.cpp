// §21.2.1.2: Size of displayed data

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DisplayWithFormatSpecifiers) {
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
