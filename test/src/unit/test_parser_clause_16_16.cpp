#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.16(b1): a property or sequence declared inside a clocking block inherits
// the block's clocking event and may not carry its own. A property whose body
// has no explicit leading clocking event is therefore legal there. Built from
// the real §14.3 clocking_declaration syntax and driven through the parser.
TEST(ClockResolutionParse, ClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      $fell(c) |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.16(b1): a property declared inside a clocking block that opens its body
// with an explicit leading clocking event is illegal.
TEST(ClockResolutionParse, ClockingBlockPropertyWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      @(posedge clk) a |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.16(b1): a sequence declared inside a clocking block with no explicit
// leading clocking event is legal; it takes the block's event.
TEST(ClockResolutionParse, ClockingBlockSequenceWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.16(b1): the LRM's own illegal example -- a sequence inside a clocking
// block whose body specifies an explicit clocking event -- is rejected.
TEST(ClockResolutionParse, ClockingBlockSequenceWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.16(b1): the prohibition is scoped to clocking blocks. The identical
// property, declared at module scope, legally carries an explicit leading
// clocking event -- confirming the check keys off placement inside the block,
// not a blanket ban on a leading clock.
TEST(ClockResolutionParse,
     ExplicitClockLegalOnDeclarationOutsideClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  property p1;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.16(b1): the rule applies inside a default clocking block too, where the
// default clocking event is the declarations' leading clock. A nested property
// with no explicit event parses cleanly (mirrors the LRM "legal: no clocking
// event" example).
TEST(ClockResolutionParse, DefaultClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic c, clk;\n"
      "  default clocking pc @(posedge clk);\n"
      "    property p3;\n"
      "      $fell(c) |=> c;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.16(b2): a multiclocked property is not allowed inside a clocking block.
// Here the body's leading term inherits the block clock while a later term
// carries its own event -- two distinct clocks -- so the declaration is
// multiclocked and rejected. This is the b2 case a leading-clock check alone
// would miss, since the body does not open with an explicit event.
TEST(ClockResolutionParse, ClockingBlockMulticlockedPropertyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      a |=> @(negedge clk) b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.16(b2): a multiclocked sequence with a non-leading clocking event is
// rejected inside a clocking block.
TEST(ClockResolutionParse, ClockingBlockMulticlockedSequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.16(b2): a sequence carrying two explicit clocking events is likewise
// multiclocked and rejected inside a clocking block -- the count>=2 form,
// distinct from the single non-leading event above.
TEST(ClockResolutionParse, ClockingBlockSequenceWithTwoClocksIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
