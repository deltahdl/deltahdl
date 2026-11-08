#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

constexpr const char* kSrff =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  initial q = 1'b1;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    f 0 : 1 : - ;\n"
    "    0 r : ? : 0 ;\n"
    "    0 f : 0 : - ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueIsOutputAtSimulationStart) {
  auto r = Parse(kSrff);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_TRUE(r.cu->udps[0]->has_initial);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '1');
}

constexpr const char* kSrffNoInitial =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    0 r : ? : 0 ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, OptionalInitialLeavesOutputUnknown) {
  auto r = Parse(kSrffNoInitial);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_FALSE(r.cu->udps[0]->has_initial);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
}

constexpr const char* kSrffInitX =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  initial q = 1'bx;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    0 r : ? : 0 ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueXSeedsUnknownStartState) {
  auto r = Parse(kSrffInitX);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_TRUE(r.cu->udps[0]->has_initial);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
}

constexpr const char* kHoldInitOne =
    "primitive hold (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  initial q = 1'b1;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : 1 : 1 ;\n"
    "    0 : 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kHoldInitZero =
    "primitive hold (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  initial q = 1'b0;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : 1 : 1 ;\n"
    "    0 : 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueServesAsCurrentState) {
  auto high = Parse(kHoldInitOne);
  ASSERT_NE(high.cu, nullptr);
  EXPECT_FALSE(high.has_errors);
  ASSERT_EQ(high.cu->udps.size(), 1u);

  auto low = Parse(kHoldInitZero);
  ASSERT_NE(low.cu, nullptr);
  EXPECT_FALSE(low.has_errors);
  ASSERT_EQ(low.cu->udps.size(), 1u);

  UdpEvalState state_high(*high.cu->udps[0]);
  EXPECT_EQ(state_high.GetOutput(), '1');
  EXPECT_EQ(state_high.Evaluate({'0'}), '1');

  UdpEvalState state_low(*low.cu->udps[0]);
  EXPECT_EQ(state_low.GetOutput(), '0');
  EXPECT_EQ(state_low.Evaluate({'0'}), '0');
}

TEST(UdpInitialStatementRun, InitialValueWithUndrivenInputsReachesTheGates) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive dff1 (q, clk, d);\n"
                       "  input clk, d;\n"
                       "  output q; reg q;\n"
                       "  initial q = 1'b1;\n"
                       "  table\n"
                       "    r 0 : ? : 0 ;\n"
                       "    r 1 : ? : 1 ;\n"
                       "    f ? : ? : - ;\n"
                       "    ? * : ? : - ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module dff (q, qb, clk, d);\n"
                       "  input clk, d;\n"
                       "  output q, qb;\n"
                       "  dff1 g1(qi, clk, d);\n"
                       "  buf #3 g2(q, qi);\n"
                       "  not #5 g3(qb, qi);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire clk, d; wire q, qb;\n"
                       "  dff u(q, qb, clk, d);\n"
                       "  initial begin\n"
                       "    #0 $display(\"qi=%b\", u.qi);\n"
                       "    #1 $display(\"q=%b qb=%b\", q, qb);\n"
                       "    #3 $display(\"q=%b qb=%b\", q, qb);\n"
                       "    #2 $display(\"q=%b qb=%b\", q, qb);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "qi=1\nq=x qb=x\nq=1 qb=x\nq=1 qb=0\n");
}

TEST(UdpInitialStatementRun, ZInputsKeepTheInitialValueAsXInputsDo) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive dff1 (q, clk, d);\n"
                       "  input clk, d;\n"
                       "  output q; reg q;\n"
                       "  initial q = 1'b1;\n"
                       "  table\n"
                       "    r 0 : ? : 0 ;\n"
                       "    r 1 : ? : 1 ;\n"
                       "    f ? : ? : - ;\n"
                       "    ? * : ? : - ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module top;\n"
                       "  wire clk, d; wire qi; reg rclk, rd; wire qr;\n"
                       "  dff1 g1(qi, clk, d);\n"
                       "  dff1 g2(qr, rclk, rd);\n"
                       "  initial begin\n"
                       "    #1 $display(\"wire-z inputs qi=%b  reg-x inputs "
                       "qr=%b\", qi, qr);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "wire-z inputs qi=1  reg-x inputs qr=1\n");
}

TEST(UdpInitialStatementRun, InitialValueIsOnTheNetAtTimeZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive srff (q, s, r);\n"
                       "  output q; reg q;\n"
                       "  input s, r;\n"
                       "  initial q = 1'b1;\n"
                       "  table\n"
                       "    1 0 : ? : 1 ;\n"
                       "    f 0 : 1 : - ;\n"
                       "    0 r : ? : 0 ;\n"
                       "    0 f : 0 : - ;\n"
                       "    1 1 : ? : 0 ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module top;\n"
                       "  reg s, r; wire q;\n"
                       "  srff u(q, s, r);\n"
                       "  initial begin\n"
                       "    $display(\"t0 %b\", q);\n"
                       "    #0 $display(\"t0+ %b\", q);\n"
                       "    #1 $display(\"t1 %b\", q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t0 1\nt0+ 1\nt1 1\n");
}

}  // namespace
