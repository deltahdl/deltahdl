#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.13.2: the multiclocked overlapping implication `|->`, where the
// antecedent and the consequent each carry their own clocking event. The
// A.2.10 file test_parser_annex_a_02_10c.cpp carries the same source as the
// `clocking_event property_expr` BNF production case.
TEST(AssertionDeclParsing, PropertyExpr_MulticlockedOverlappingImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, MultichannelAssertPropertyInline) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.13.2: the multiclock nonoverlapping implication `|=>` as the body of a
// named property declaration. The A.2.10 file test_parser_annex_a_02_10c.cpp
// carries the same source as the `property_declaration` production case.
TEST(AssertionParsing, MulticlockedNonoverlappingImplicationInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_multi;\n"
      "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.13.2: a multiclocked property may be formed with a Boolean property
// operator over two differently clocked operands. This is the
// `(@(posedge clk0) sig0) and (@(posedge clk1) sig1)` syntactic position, which
// is a multiclocked property but not a multiclocked sequence — the parser must
// accept it as a property spec.
TEST(AssertionParsing, MulticlockedBooleanAndOfClockedOperands) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    (@(posedge clk0) sig0) and (@(posedge clk1) sig1)\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.13.2: the multiclocked if / if-else syntactic position, where the
// condition is checked on the property clock and each branch carries its own
// clocking event.
TEST(AssertionParsing, MulticlockedIfElseProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk0) if (b) @(posedge clk1) s1\n"
      "    else @(posedge clk2) s2\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.13.2: the combination example — a nonoverlapping implication whose
// consequent is itself a Boolean `and` of two differently clocked properties:
// `@(posedge clk0) s0 |=> (@(posedge clk1) s1) and (@(posedge clk2) s2)`.
TEST(AssertionParsing, MulticlockedImplicationWithBooleanAndConsequent) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk0) s0 |=>\n"
      "      (@(posedge clk1) s1) and (@(posedge clk2) s2)\n"
      "  );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
