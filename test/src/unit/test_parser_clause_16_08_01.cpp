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

TEST(TypedSequenceFormalSyntax, IntegralTypedFormalAccepted) {
  // §16.8.1: a typed formal may carry one of the data types allowed in §16.6,
  // which includes the integral types. The `event`/`sequence`/`untyped`
  // keywords are not the only spellings the parser must admit in the type
  // slot; a plain data type such as `bit` or `byte` is equally valid.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(bit x, byte y);\n"
              "    x ##1 y;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, BareFormalAfterTypedInheritsType) {
  // §16.8.1: an untyped formal following a data type must spell `untyped`;
  // absent that keyword a bare identifier inherits the preceding type. Here
  // `shortint` applies to both `delay1` and `delay2`, while `max` (before any
  // type) and `min` (there is no type before it) stay untyped. The parser must
  // accept this shared-type shape without demanding a type on every formal.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence d(max, shortint delay1, delay2, min);\n"
              "    1'b1 ##delay1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, UserDefinedTypeTypedFormalAccepted) {
  // §16.8.1: the types allowed for a typed formal (those of §16.6) include
  // user-defined types, so a typedef name is a valid formal type — a distinct
  // input form from the built-in integral keywords.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef logic [3:0] nibble_t;\n"
              "  sequence s(nibble_t x);\n"
              "    x[0] ##1 x[1];\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
