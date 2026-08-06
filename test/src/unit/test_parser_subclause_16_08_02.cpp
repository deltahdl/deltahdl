#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.8.2: a sequence formal argument may be designated as a local variable
// argument with the keyword `local`. The parser records each local-marked
// formal so later stages can apply the §16.10 local-variable rules.
TEST(SequenceLocalLvarArgumentParsing, LocalKeywordOnSequenceFormalParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  // §16.8.2: if no direction is specified, the inferred direction is `input`.
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

// §16.8.2: an explicit `input`/`inout`/`output` after `local` is captured as
// the direction of the local variable formal argument.
TEST(SequenceLocalLvarArgumentParsing, LocalDirectionsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic a,\n"
      "             local inout int b,\n"
      "             local output bit c);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 3u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[2], Direction::kOutput);
}

// §16.8.2: a direction without `local` in a sequence port item is illegal.
TEST(SequenceLocalLvarArgumentParsing, DirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(output logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: the `local`-required-with-direction rule holds for `input` too — an
// `input` direction with no preceding `local` keyword is illegal. (Negative
// input form: direction keyword `input`.)
TEST(SequenceLocalLvarArgumentParsing, InputDirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(input logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: likewise for `inout` — a direction keyword without a preceding
// `local` is illegal. (Negative input form: direction keyword `inout`.)
TEST(SequenceLocalLvarArgumentParsing, InoutDirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(inout int b);\n"
      "    @(posedge clk) b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: it shall be illegal to specify a default actual argument for a
// local variable argument of direction inout.
TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnInoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout int b = 1);\n"
      "    @(posedge clk) b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: it shall be illegal to specify a default actual argument for a
// local variable argument of direction output.
TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnOutputLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local output bit c = 0);\n"
      "    @(posedge clk) c;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: a local input formal may have a default actual argument; this is
// permitted and must parse without diagnostic.
TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnInputLocalParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic a = 1'b1);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

// §16.8.2: a port item that supplies only an identifier inherits the local
// designation, direction, and type of the nearest preceding port item that
// declared them explicitly.
TEST(SequenceLocalLvarArgumentParsing, IdentifierOnlyItemInheritsLocalDir) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout logic a, b, c);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 3u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
  EXPECT_EQ(item->prop_formals[2], "c");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 3u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[2], Direction::kInout);
}

// §16.8.2: when the `local` keyword is specified in a port item, the type of
// that argument must be specified explicitly in the same port item — it
// cannot be inferred from a previous argument and is not allowed to be
// omitted.
TEST(SequenceLocalLvarArgumentParsing, LocalWithoutExplicitTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: a port item with `local` whose type is a user-defined type alias
// satisfies the explicit-type requirement — the leading identifier is the
// type, the trailing identifier is the formal name.
TEST(SequenceLocalLvarArgumentParsing, LocalWithUserDefinedTypeParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local my_type_t a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

// §16.8.2: the carry breaks at any port item that introduces an explicit type
// keyword. A typed-but-non-local port item is not a local variable formal.
TEST(SequenceLocalLvarArgumentParsing, ExplicitTypeBreaksLocalCarry) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local logic a, bit b);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  // Only one local-marked formal: the explicit `bit b` is a fresh, non-local
  // port item that breaks the carry from the preceding `local logic a`.
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

// §16.8.2: the type of a local variable formal argument shall be one of the
// types allowed in §16.6. `event` is a formal-type category permitted for an
// ordinary formal (§16.8.1) but is not a §16.6 data type, so it is rejected
// when used as the type of a `local` formal — this is the negative form of the
// type restriction, mirroring the `local event e` line of the illegal example.
TEST(SequenceLocalLvarArgumentParsing, LocalEventTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local event e);\n"
      "    @(posedge clk) e;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: `property` is a formal-type category (§16.12.19) but not a §16.6
// data type, so it too is rejected as the type of a `local` formal. (Negative
// input form: disallowed type keyword `property`.)
TEST(SequenceLocalLvarArgumentParsing, LocalPropertyTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local property p);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.8.2: `sequence` and `untyped`, though legal formal-type categories for a
// non-local formal, are likewise not §16.6 data types and so are rejected as
// the type of a `local` formal.
TEST(SequenceLocalLvarArgumentParsing, LocalSequenceOrUntypedTypeIsError) {
  auto r1 = Parse(
      "module m;\n"
      "  sequence s(local sequence q);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r1.has_errors);
  auto r2 = Parse(
      "module m;\n"
      "  sequence s(local untyped u);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(r2.has_errors);
}

// §16.8.2: a local formal whose type IS one of the §16.6 data types (here the
// integral keyword `int`) is accepted — the positive companion to the rejected
// non-§16.6 categories above.
TEST(SequenceLocalLvarArgumentParsing, LocalSixteenSixTypeParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local int lv);\n"
      "    @(posedge clk) lv;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

// §16.8.2: the carry of a local designation ends not only at an explicit type
// but also at a subsequent port item that itself specifies the `local`
// keyword. A fresh `local` opens an independent local variable formal with its
// own direction and type — here the second item restarts as `local input bit`,
// so the two formals carry different directions rather than the first's `inout`
// propagating onto the second.
TEST(SequenceLocalLvarArgumentParsing, SubsequentLocalRestartsCarry) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout logic a, local input bit b);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 2u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInput);
}

}  // namespace
