#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

}
