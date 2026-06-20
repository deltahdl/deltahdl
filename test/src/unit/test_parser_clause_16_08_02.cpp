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

}  // namespace
