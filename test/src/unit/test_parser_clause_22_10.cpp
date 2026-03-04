#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`celldefine\n"
                              "module inv(output y, input a);\n"
                              "  assign y = ~a;\n"
                              "endmodule\n"
                              "`endcelldefine\n"));
}

}  // namespace
