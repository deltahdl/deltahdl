#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull1\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`unconnected_drive pull0\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

}
