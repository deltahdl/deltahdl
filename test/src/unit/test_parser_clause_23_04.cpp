// §23.4: Nested modules

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

using ProgramParseTest = ProgramTestParse;

namespace {

// =========================================================================
// LRM section 23.4: Nested modules
// =========================================================================
TEST(ParserSection23, NestedModuleParsesOk) {
  EXPECT_TRUE(
      ParseOk("module outer;\n"
              "  wire w;\n"
              "  module inner;\n"
              "    assign w = 1'b1;\n"
              "  endmodule\n"
              "  inner i1();\n"
              "endmodule\n"));
}

TEST(ParserSection23, NestedModuleMultiple) {
  EXPECT_TRUE(
      ParseOk("module outer(input d, ck, output q, nq);\n"
              "  wire q1, nq1;\n"
              "  module ff1;\n"
              "    nand g1(nq1, d, q1);\n"
              "  endmodule\n"
              "  ff1 i1();\n"
              "  module ff2;\n"
              "    nand g2(q1, ck, nq1);\n"
              "  endmodule\n"
              "  ff2 i2();\n"
              "endmodule\n"));
}

}  // namespace
