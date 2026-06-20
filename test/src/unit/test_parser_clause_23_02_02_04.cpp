

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DefaultPortValueParsing, MultiplePortsSomeWithDefaults) {
  auto r = Parse(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 1'b0,\n"
      "  input logic [7:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->ports[2].default_value, nullptr);
}

TEST(DefaultPortValueParsing, OutputWithDefaultValue) {
  // The parser is direction-agnostic about defaults: it accepts a trailing
  // "= expr" on any direction and records it. Rejecting a default on a
  // non-input port is a semantic rule applied later by the elaborator (see
  // §23.2.2.4 C3), so this clean parse is what makes that elaborator test a
  // genuine observer rather than a parse-error false-pass.
  auto r = Parse("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DefaultPortValueParsing, NonAnsiPortDefaultRejected) {
  // §23.2.2.4: a default value may be given only in ANSI-style declarations.
  // The non-ANSI port grammar carries no "= constant_expression" production, so
  // attaching a default to a non-ANSI body port declaration is rejected here at
  // the parser stage (the trailing "=" has nowhere to bind and breaks the
  // declaration). Contrast with the ANSI-style defaults above, which parse
  // cleanly.
  auto r = Parse(
      "module m(a);\n"
      "  input logic a = 1'b0;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
