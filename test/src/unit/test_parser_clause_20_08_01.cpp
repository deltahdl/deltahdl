// §20.8.1: Integer math functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
}

}  // namespace
