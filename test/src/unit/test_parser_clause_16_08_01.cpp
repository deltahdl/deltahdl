#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TypedSequenceFormalSyntax, UntypedKeywordAccepted) {
  // §16.8.1: a formal argument's data type may be the keyword `untyped`.
  // The parser must accept that keyword in the same syntactic slot as a
  // regular type.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x, untyped y);\n"
              "    x ##1 y;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, SequenceTypedFormalAccepted) {
  // §16.8.1(a): a formal may be typed `sequence`.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence inner;\n"
              "    1'b1 ##1 1'b1;\n"
              "  endsequence\n"
              "  sequence s(sequence q);\n"
              "    q ##1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, EventTypedFormalAccepted) {
  // §16.8.1(b): a formal may be typed `event`.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(event ev);\n"
              "    @(ev) 1'b1 ##1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
