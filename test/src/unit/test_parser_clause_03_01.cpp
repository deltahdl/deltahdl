// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilationUnitStructure, MissingEndconfigIsError) {
  EXPECT_FALSE(ParseOk(
      "module m; endmodule\n"
      "config c;\n"
      "  design m;"));
}

TEST(CompilationUnitStructure, MissingEndprimitiveIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"));
}

}  // namespace
