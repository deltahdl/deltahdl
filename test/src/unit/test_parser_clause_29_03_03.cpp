#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(ParserAnnexA051, SequentialWithInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, input r);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(ParserAnnexA051, SequentialInitialX) {
  auto r = Parse(
      "primitive dff_x(output reg q, input d, input clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, 'x');
}

TEST(ParserAnnexA051, SimSequentialWithInitial) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '0');
}

TEST(ParserAnnexA053, SeqBody_WithInitial) {
  auto r = Parse(
      "primitive latch_init(output reg q, input d, en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  EXPECT_EQ(udp->table.size(), 3);
}

TEST(ParserAnnexA053, SeqBody_SimInitialValue) {
  auto r = Parse(
      "primitive latch_init(output reg q, input d, en);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  EXPECT_EQ(eval.GetOutput(), '1');

  eval.Evaluate({'0', '0'});
  EXPECT_EQ(eval.GetOutput(), '1');
}

TEST(ParserAnnexA053, InitStmt_ValueOne) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(ParserAnnexA053, InitVal_1b0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(ParserAnnexA053, InitVal_1b1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(ParserAnnexA053, InitVal_1bx) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(ParserAnnexA053, InitVal_1bX) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'bX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(ParserAnnexA053, InitVal_1B0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'B0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(ParserAnnexA053, InitVal_1B1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'B1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(ParserAnnexA053, InitVal_1Bx) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'Bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(ParserAnnexA053, InitVal_1BX) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'BX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(ParserAnnexA053, InitVal_Bare0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(ParserAnnexA053, InitVal_Bare1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(ParserClause03, Cl3_7_SequentialUdp) {
  auto r = Parse(
      "primitive udp_latch (output reg q, input d, en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_latch");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  ASSERT_EQ(udp->table.size(), 3u);

  EXPECT_EQ(udp->table[0].current_state, '?');
  EXPECT_EQ(udp->table[0].output, '1');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(ParserSection29, SequentialUdpInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

}
