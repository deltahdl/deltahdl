// §22.10: `celldefine and `endcelldefine

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseOk("`celldefine\n"
              "module inv(output y, input a);\n"
              "  assign y = ~a;\n"
              "endmodule\n"
              "`endcelldefine\n"));
}

}  // namespace
