// §28.6: bufif1, bufif0, notif1, and notif0 gates

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (enable_gatetype alternative)
// gate_instantiation ::=
//   enable_gatetype [drive_strength] [delay3] enable_gate_instance
//                   {, enable_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_Bufif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Notif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Notif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.1 Production #3: enable_gate_instance
// enable_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , enable_terminal )
// =============================================================================
TEST(ParserA301, EnableGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, EnableGateInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  notif1 n1(out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_AllEnableGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 b0(o, i, c);\n"
              "  bufif1 b1(o, i, c);\n"
              "  notif0 n0(o, i, c);\n"
              "  notif1 n1(o, i, c);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.4 Production #2: enable_gatetype ::= bufif0 | bufif1 | notif0 | notif1
// =============================================================================
TEST(ParserA304, EnableGatetype_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, EnableGatetype_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, EnableGatetype_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

}  // namespace
