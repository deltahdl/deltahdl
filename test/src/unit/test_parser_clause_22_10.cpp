#include "fixture_parser.h"

using namespace delta;

namespace {

// §22.10 has no parser-stage rule: the `celldefine/`endcelldefine directives
// are consumed by the preprocessor and reach the parser as ordinary source.
// One representative check that a cell-tagged module parses is sufficient;
// the directive-placement variations are observed in the preprocessor tests.
TEST(CompilerDirectiveParsing, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`celldefine\n"
                              "module inv(output y, input a);\n"
                              "  assign y = ~a;\n"
                              "endmodule\n"
                              "`endcelldefine\n"));
}

}  // namespace
