// §29.3.3: Sequential UDP initial statement

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: sequential with initial statement ---
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

// --- udp_declaration: sequential with initial value x ---
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

// --- Sequential UDP evaluation with initial value ---
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

// Sequential body with initial statement
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

}  // namespace
