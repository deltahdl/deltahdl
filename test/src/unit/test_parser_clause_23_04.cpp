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

}  // namespace
