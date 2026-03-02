// §22.8: `default_nettype

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefaultNettypeTri) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri\n"
              "module t;\n"
              "endmodule\n"));
}

}  // namespace
