// §30.5.1: Specifying transition delays on module paths

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using ConfigParseTest = ProgramTestParse;

namespace {

TEST(ParserSection28, Sec28_12_SpecparamMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify\n"
              "    specparam tPLH = 3:5:7;\n"
              "    (a => b) = tPLH;\n"
              "  endspecify\n"
              "endmodule\n"));
}

}  // namespace
