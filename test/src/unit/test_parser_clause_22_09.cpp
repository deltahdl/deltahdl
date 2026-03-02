// §22.9: `unconnected_drive and `nounconnected_drive

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull1\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

}  // namespace
