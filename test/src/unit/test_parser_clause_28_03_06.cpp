// §28.3.6: Primitive instance connection list

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_ComplexTerminalExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and a1(out[0], in1[3:0], in2[7:4]);\n"
              "endmodule\n"));
}

}  // namespace
