#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

char EvaluateEdgeOnFirstInput(const UdpDecl& decl, char from, char to) {
  UdpEvalState s(decl);
  s.SetInputs({from, '1'});
  return s.EvaluateWithEdge({to, '1'}, 0, from);
}

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
  EXPECT_EQ(s.Evaluate({'x', '0'}), 'x');
}

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
  EXPECT_EQ(s.Evaluate({'x', '0'}), 'x');
  EXPECT_EQ(s.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');
}

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
  EXPECT_EQ(s.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(s.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(s.Evaluate({'0', '1'}), '0');
}

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
    EXPECT_EQ(s.EvaluateWithEdge({'1', '0'}, 0, '0'), '1');
  }
  {
    UdpEvalState s(*r.cu->udps[0]);
    s.SetInputs({'1', '0'});
    EXPECT_EQ(s.EvaluateWithEdge({'1', '0'}, 0, '1'), 'x');
  }
}

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
    EXPECT_EQ(a.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');
    EXPECT_EQ(b.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');
  }
  {
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
    EXPECT_EQ(a.EvaluateWithEdge({'0', '1'}, 0, '1'), '0');
    EXPECT_EQ(b.EvaluateWithEdge({'0', '1'}, 0, '1'), '0');
  }
  {
    UdpEvalState a(*shorthand.cu->udps[0]);
    UdpEvalState b(*paren.cu->udps[0]);
    a.SetInputs({'0', '1'});
    b.SetInputs({'0', '1'});
    EXPECT_EQ(a.EvaluateWithEdge({'1', '1'}, 0, '0'), 'x');
    EXPECT_EQ(b.EvaluateWithEdge({'1', '1'}, 0, '0'), 'x');
  }
}

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
  const Case kCases[] = {
      {'0', '1', '1'}, {'0', 'x', '1'}, {'x', '1', '1'}, {'1', '0', 'x'}};
  for (const auto& c : kCases) {
    UdpEvalState s(decl);
    s.SetInputs({c.from, '1'});
    EXPECT_EQ(s.EvaluateWithEdge({c.to, '1'}, 0, c.from), c.expected)
        << c.from << "->" << c.to;
  }
}

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
  const Case kCases[] = {
      {'1', '0', '0'}, {'1', 'x', '0'}, {'x', '0', '0'}, {'0', '1', 'x'}};
  for (const auto& c : kCases) {
    UdpEvalState s(decl);
    s.SetInputs({c.from, '1'});
    EXPECT_EQ(s.EvaluateWithEdge({c.to, '1'}, 0, c.from), c.expected)
        << c.from << "->" << c.to;
  }
}

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
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, '1', 'x'), '0');
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, '1', '0'), 'x');
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
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, '0', '1'), '0');
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, 'x', '1'), '0');
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, '0', '0'), 'x');
}

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
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, '0', '1'), '0');
  EXPECT_EQ(EvaluateEdgeOnFirstInput(decl, 'x', '1'), 'x');
}

TEST(UdpSymbolSemantics, UpperCaseSymbolsMatchAsTheLowerCaseOnesDo) {
  SimFixture f;
  auto out = RunCapture(
      "primitive pass1 (o, a, b);\n"
      "  output o; input a, b;\n"
      "  table 1 X : 1 ; 0 ? : 0 ; endtable\n"
      "endprimitive\n"
      "primitive dff (q, clk, d);\n"
      "  output q; reg q; input clk, d;\n"
      "  table R 1 : ? : 1 ; R 0 : ? : 0 ; F ? : B : - ; ? * : ? : - ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  reg a = 1, b = 1'bx, clk = 0, d = 1;\n"
      "  wire o, q;\n"
      "  pass1 u1 (o, a, b);\n"
      "  dff u2 (q, clk, d);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 $display(\"%b %b\", o, q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
