#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

}
