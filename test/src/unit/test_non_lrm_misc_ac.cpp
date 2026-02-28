// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

}  // namespace
