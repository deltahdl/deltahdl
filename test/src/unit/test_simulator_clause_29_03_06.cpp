// §29.3.6 "Summary of symbols" (Table 29-1) defines the meaning of every
// special symbol usable in a UDP state table. These simulator-stage tests build
// each UDP from real `primitive` source (parsed through the pipeline) and then
// drive UdpEvalState to observe the symbol-matching semantics carried in
// udp_eval.cpp:
//   ?    matches 0, 1, or x            b    matches 0 or 1
//   -    keeps the current output      (vw) matches a change from v to w
//   *    matches any input change      r    matches a (01) rising edge
//   f    matches a (10) falling edge   p    matches (01), (0x), or (x1)
//   n    matches (10), (1x), or (x0)
//
// The complementary field-permission rules are exercised in the parser
// canonical file for this subclause.
#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// ? in an input field matches any of 0, 1, or x.
TEST(UdpSymbolSemantics, QuestionMatchesZeroOneAndX) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    ? 0 : 1;\n"
      "    ? 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  UdpEvalState s(*r.cu->udps[0]);
  EXPECT_EQ(s.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'x', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'0', '1'}), '0');
}

// b in an input field matches 0 or 1, but not x.
TEST(UdpSymbolSemantics, BMatchesZeroAndOneNotX) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    b 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  UdpEvalState s(*r.cu->udps[0]);
  EXPECT_EQ(s.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');
  // x is not covered by b, and no other row matches -> default output x.
  EXPECT_EQ(s.Evaluate({'x', '0'}), 'x');
}

// x is the unknown value symbol: an x input cell matches a runtime x and no
// other level, and an x output cell drives the output to x.
TEST(UdpSymbolSemantics, XLevelSymbolMatchesOnlyXAndDrivesXOutput) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x 0 : x;\n"
      "    0 0 : 0;\n"
      "    1 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  UdpEvalState s(*r.cu->udps[0]);
  EXPECT_EQ(s.Evaluate({'x', '0'}), 'x');  // x cell matches x, output x
  EXPECT_EQ(s.Evaluate({'0', '0'}), '0');  // 0 falls through to its own row
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');  // 1 falls through to its own row
}

// - in the output field of a sequential UDP holds the previous output value.
TEST(UdpSymbolSemantics, DashOutputKeepsPreviousValue) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  UdpEvalState s(*r.cu->udps[0]);
  EXPECT_EQ(s.Evaluate({'1', '1'}), '1');  // en=1 -> follow d
  EXPECT_EQ(s.Evaluate({'0', '0'}), '1');  // en=0 -> hold (-)
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');  // en=0 -> still holding
  EXPECT_EQ(s.Evaluate({'0', '1'}), '0');  // en=1 -> follow d again
}

// * matches any value change on the transitioning input; no change -> no match.
TEST(UdpSymbolSemantics, StarMatchesAnyInputChange) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    * 0 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  {
    UdpEvalState s(*r.cu->udps[0]);
    s.SetInputs({'0', '0'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '0'}, 0, '0'), '1');  // 0->1 changed
  }
  {
    UdpEvalState s(*r.cu->udps[0]);
    s.SetInputs({'1', '0'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '0'}, 0, '1'), 'x');  // no change
  }
}

// r is a rising edge, equivalent to (01); f is a falling edge, equivalent to
// (10). Verify r and (01) behave identically, and likewise for f and (10).
TEST(UdpSymbolSemantics, RisingEdgeEquivalentToParen01) {
  auto shorthand = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    r 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  auto paren = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (01) 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(shorthand.has_errors);
  ASSERT_FALSE(paren.has_errors);
  {
    UdpEvalState a(*shorthand.cu->udps[0]);
    UdpEvalState b(*paren.cu->udps[0]);
    a.SetInputs({'0', '1'});
    b.SetInputs({'0', '1'});
    EXPECT_EQ(a.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');  // rising -> 1
    EXPECT_EQ(b.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');
  }
  {
    // A falling edge is not a rising edge, so neither row matches -> x.
    UdpEvalState a(*shorthand.cu->udps[0]);
    UdpEvalState b(*paren.cu->udps[0]);
    a.SetInputs({'1', '1'});
    b.SetInputs({'1', '1'});
    EXPECT_EQ(a.EvaluateWithEdge({'0', '1'}, 0, '1'), 'x');
    EXPECT_EQ(b.EvaluateWithEdge({'0', '1'}, 0, '1'), 'x');
  }
}

TEST(UdpSymbolSemantics, FallingEdgeEquivalentToParen10) {
  auto shorthand = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    f 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  auto paren = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (10) 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(shorthand.has_errors);
  ASSERT_FALSE(paren.has_errors);
  {
    UdpEvalState a(*shorthand.cu->udps[0]);
    UdpEvalState b(*paren.cu->udps[0]);
    a.SetInputs({'1', '1'});
    b.SetInputs({'1', '1'});
    EXPECT_EQ(a.EvaluateWithEdge({'0', '1'}, 0, '1'), '0');  // falling -> 0
    EXPECT_EQ(b.EvaluateWithEdge({'0', '1'}, 0, '1'), '0');
  }
  {
    // A rising edge is not a falling edge, so neither row matches -> x.
    UdpEvalState a(*shorthand.cu->udps[0]);
    UdpEvalState b(*paren.cu->udps[0]);
    a.SetInputs({'0', '1'});
    b.SetInputs({'0', '1'});
    EXPECT_EQ(a.EvaluateWithEdge({'1', '1'}, 0, '0'), 'x');
    EXPECT_EQ(b.EvaluateWithEdge({'1', '1'}, 0, '0'), 'x');
  }
}

// p is a potential positive edge: iteration of (01), (0x), and (x1). A negative
// transition does not match.
TEST(UdpSymbolSemantics, PMatchesPotentialPositiveEdges) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    p 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  const UdpDecl& decl = *r.cu->udps[0];
  struct Case {
    char from, to, expected;
  };
  const Case cases[] = {
      {'0', '1', '1'}, {'0', 'x', '1'}, {'x', '1', '1'}, {'1', '0', 'x'}};
  for (const auto& c : cases) {
    UdpEvalState s(decl);
    s.SetInputs({c.from, '1'});
    EXPECT_EQ(s.EvaluateWithEdge({c.to, '1'}, 0, c.from), c.expected)
        << c.from << "->" << c.to;
  }
}

// n is a potential negative edge: iteration of (10), (1x), and (x0). A positive
// transition does not match.
TEST(UdpSymbolSemantics, NMatchesPotentialNegativeEdges) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    n 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  const UdpDecl& decl = *r.cu->udps[0];
  struct Case {
    char from, to, expected;
  };
  const Case cases[] = {
      {'1', '0', '0'}, {'1', 'x', '0'}, {'x', '0', '0'}, {'0', '1', 'x'}};
  for (const auto& c : cases) {
    UdpEvalState s(decl);
    s.SetInputs({c.from, '1'});
    EXPECT_EQ(s.EvaluateWithEdge({c.to, '1'}, 0, c.from), c.expected)
        << c.from << "->" << c.to;
  }
}

// (vw) matches a value change whose endpoints are the level symbols v and w;
// the endpoints may themselves be iterated symbols such as ?.
TEST(UdpSymbolSemantics, ParenEdgeMatchesSpecifiedTransition) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (1x) 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  const UdpDecl& decl = *r.cu->udps[0];
  {
    UdpEvalState s(decl);
    s.SetInputs({'1', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'x', '1'}, 0, '1'), '0');  // 1->x matches
  }
  {
    UdpEvalState s(decl);
    s.SetInputs({'1', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'0', '1'}, 0, '1'), 'x');  // 1->0 does not
  }
}

TEST(UdpSymbolSemantics, ParenEdgeQuestionEndpointAdmitsAllLevels) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (?1) 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  const UdpDecl& decl = *r.cu->udps[0];
  {
    UdpEvalState s(decl);
    s.SetInputs({'0', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');  // 0->1, ? admits 0
  }
  {
    UdpEvalState s(decl);
    s.SetInputs({'x', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '1'}, 0, 'x'), '0');  // x->1, ? admits x
  }
  {
    UdpEvalState s(decl);
    s.SetInputs({'0', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'0', '1'}, 0, '0'), 'x');  // to must be 1
  }
}

// A (vw) endpoint may be the iterated symbol b, which admits 0 and 1 but not x.
TEST(UdpSymbolSemantics, ParenEdgeBEndpointMatchesBitValuesNotX) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (b1) 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->udps.empty());
  const UdpDecl& decl = *r.cu->udps[0];
  {
    UdpEvalState s(decl);
    s.SetInputs({'0', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');  // 0->1, b admits 0
  }
  {
    UdpEvalState s(decl);
    s.SetInputs({'x', '1'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '1'}, 0, 'x'),
              'x');  // x->1, b excludes x
  }
}

}  // namespace
