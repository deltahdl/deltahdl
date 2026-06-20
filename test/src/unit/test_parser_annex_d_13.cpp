#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.13: $showvars may appear with no argument, parsing as an ordinary
// system task call.
TEST(OptionalSystemTaskParserParsing, ShowVarsNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showvars;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.13: $showvars accepts a parenthesized list of variables.
TEST(OptionalSystemTaskParserParsing, ShowVarsVariableList) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial $showvars(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.13: a variable in the list may be a bit-select or part-select of a
// vector.
TEST(OptionalSystemTaskParserParsing, ShowVarsSelectArgument) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  initial $showvars(v[3], v[5:2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.13: a single-variable list is the minimal parenthesized form.
TEST(OptionalSystemTaskParserParsing, ShowVarsSingleVariable) {
  auto r = Parse(
      "module m;\n"
      "  reg x;\n"
      "  initial $showvars(x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.13: an indexed part-select of a vector is also a valid list entry,
// exercising the +: part-select syntax rather than a plain range.
TEST(OptionalSystemTaskParserParsing, ShowVarsIndexedPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  initial $showvars(v[2+:3]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
