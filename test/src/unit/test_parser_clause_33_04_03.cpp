#include "fixture_parser.h"

namespace {

TEST(ConfigPositionalParamNotation, SinglePositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(8);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, MultiplePositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(8, 16);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, MixedNamedThenPositionalRejected) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(.W(8), 16);\n"
                 "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, NamedAssignmentAccepted) {
  auto r = Parse("config c;\n"
                 "  design top;\n"
                 "  instance top.a1 use #(.W(8));\n"
                 "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}
