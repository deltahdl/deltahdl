// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_PmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_RnmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rnmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_RpmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rpmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_MosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #10 n1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
}

TEST(ParserA301, GateInst_MosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(o1, i1, c1), p2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

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

}  // namespace
