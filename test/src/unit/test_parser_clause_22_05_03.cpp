#include "fixture_parser.h"

using namespace delta;

namespace {

// §22.5.3 puts no restriction on placement, so the directive is equally legal
// inside a design element and the module still parses.
TEST(UndefineAllParsing, UndefineAllInsideDesignElement) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "module t;\n"
                              "`undefineall\n"
                              "  wire w;\n"
                              "endmodule\n"));
}

// C2: with no arguments to take, source text left on the directive's line is
// handed to the parser as ordinary syntax rather than being consumed.
TEST(UndefineAllParsing, UndefineAllTrailingTextParsesAsSource) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "module t;\n"
                              "`undefineall wire w;\n"
                              "endmodule\n"));
}

// Once the macros are gone the conditional falls through to its `else arm, and
// what reaches the parser is the branch that arm supplies.
TEST(UndefineAllParsing, UndefineAllLeavesElseBranchToParse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "`undefineall\n"
                              "module t;\n"
                              "`ifdef A\n"
                              "  this is not valid syntax\n"
                              "`else\n"
                              "  wire w;\n"
                              "`endif\n"
                              "endmodule\n"));
}

}  // namespace
