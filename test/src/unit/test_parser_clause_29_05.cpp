// §29.5: Level-sensitive sequential UDPs

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// udp_body alternative 2: sequential_body
TEST(ParserAnnexA053, UdpBody_SequentialAlternative) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 3);
}

// Simulation: sequential body evaluates correctly
TEST(ParserAnnexA053, UdpBody_SimSequential) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  // Enable high, data=0 -> output=0
  eval.Evaluate({'0', '1'});
  EXPECT_EQ(eval.GetOutput(), '0');
  // Enable low -> no change
  eval.Evaluate({'1', '0'});
  EXPECT_EQ(eval.GetOutput(), '0');
}

// ---------------------------------------------------------------------------
// Production 8: seq_input_list ::= level_input_list | edge_input_list
// ---------------------------------------------------------------------------
// seq_input_list as level_input_list (no edge symbols)
TEST(ParserAnnexA053, SeqInputList_LevelOnly) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  // All entries use only level symbols
  for (const auto& row : udp->table) {
    for (char c : row.inputs) {
      EXPECT_TRUE(c == '0' || c == '1' || c == '?' || c == 'x' || c == 'b');
    }
  }
}

}  // namespace
