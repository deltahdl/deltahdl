#include "fixture_parser.h"

using namespace delta;

namespace {

// §20.2 Syntax 20-1: simulation_control_task ::= $stop [ ( n ) ] ;
//                                              | $finish [ ( n ) ] ;
//                                              | $exit [ ( ) ] ;
// Each control task is accepted both bare and with its optional argument.

TEST(SystemNameParserParsing, SystemTask_FinishNoArgs) {
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

TEST(SystemNameParserParsing, SystemTask_FinishWithLevel) {
  EXPECT_TRUE(ParseOk("module m; initial $finish(2); endmodule"));
}

TEST(SystemNameParserParsing, SystemTask_StopNoArgs) {
  EXPECT_TRUE(ParseOk("module m; initial $stop; endmodule"));
}

TEST(SystemNameParserParsing, SystemTask_StopWithLevel) {
  EXPECT_TRUE(ParseOk("module m; initial $stop(1); endmodule"));
}

TEST(SystemNameParserParsing, SystemTask_ExitNoArgs) {
  EXPECT_TRUE(ParseOk("module m; initial $exit; endmodule"));
}

TEST(SystemNameParserParsing, SystemTask_ExitEmptyParens) {
  EXPECT_TRUE(ParseOk("module m; initial $exit(); endmodule"));
}

}  // namespace
