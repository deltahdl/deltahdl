#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

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
