#include "fixture_parser.h"

namespace {

// §33.4.3 item 8: a configuration's use-clause parameter override
// must use the named form (`.NAME(value)`).  The parser rejects bare
// positional values such as `#(8)`.
TEST(ConfigPositionalParamNotation, SinglePositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(8);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// Multiple positional values are rejected for the same reason.
TEST(ConfigPositionalParamNotation, MultiplePositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(8, 16);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// A positional argument trailing a named one is still positional and
// is rejected on the second iteration of the parser's do-while loop.
TEST(ConfigPositionalParamNotation, MixedNamedThenPositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(.W(8), 16);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// Positive control: the named form is the only form that parses.
TEST(ConfigPositionalParamNotation, NamedAssignmentAccepted) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(.W(8));\n"
                 "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
