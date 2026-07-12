#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.18: a `property`-typed formal may appear in the consequent of an
// implication, because the consequent is a property_expr position. Placing the
// formal as the consequent of `|->` is therefore legal.
TEST(TypedPropertyFormalParsing, PropertyTypedFormalAsConsequentParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    b |-> q;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: a `property`-typed formal may not be referenced as the antecedent
// of an overlapping implication `|->` (see §16.12.7), regardless of the actual
// argument, because a property_expr may not be written in that position. The
// body scan rejects the reference standing in the antecedent position.
TEST(TypedPropertyFormalParsing,
     PropertyTypedFormalAsOverlapAntecedentRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    q |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.18: the same prohibition covers the non-overlapping implication `|=>`,
// whose antecedent is likewise a sequence_expr position where a property_expr
// may not be written.
TEST(TypedPropertyFormalParsing,
     PropertyTypedFormalAsNonOverlapAntecedentRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    q |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.18: the prohibition is specific to `property`-typed formals. A
// `sequence`-typed formal is a legal antecedent of an implication (a sequence
// may be written in the antecedent position), so the same shape with a sequence
// formal parses cleanly. This confirms the rule keys off the formal's declared
// type, not merely the syntactic position.
TEST(TypedPropertyFormalParsing, SequenceTypedFormalAsAntecedentParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(sequence q);\n"
      "    q |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: the `property` type keyword qualifies the whole comma-separated
// run of formal names until a differently typed item begins, so in `property q,
// r` both q and r are property-typed. A reference to the second name r as an
// implication antecedent is therefore rejected just as the first would be,
// confirming the carry-over of the property_formal_type across the port run.
TEST(TypedPropertyFormalParsing, PropertyTypeCarriesOverCommaSeparatedRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q, r);\n"
      "    r |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.18: the property run is ended not only by a §16.6 data type but by any
// non-property formal type keyword — `sequence`, `event`, or `untyped`. Here an
// active property run started by `property a` is cleared by the `event`
// keyword, so the second formal b is event-typed, not property-typed, and may
// legally head an implication. This exercises the run-clearing path distinct
// from the data-type case (a different type-keyword handler) and confirms the
// rule keys strictly off the `property` type.
TEST(TypedPropertyFormalParsing, EventTypeKeywordEndsActivePropertyRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property a, event b);\n"
      "    b |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: a data-type (§16.6) formal item ends the property run, so a formal
// declared after a `property` name but with an intervening data type is not
// property-typed and may legally head an implication. Here q is property-typed
// but r is `bit`-typed; referencing r as an antecedent raises no diagnostic,
// showing the run ends at the fresh type specifier.
TEST(TypedPropertyFormalParsing, DataTypeFormalEndsPropertyRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q, bit r);\n"
      "    r |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

}  // namespace
