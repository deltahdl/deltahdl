// §28.8: Bidirectional pass switches

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pass_en_switchtype alternative)
// gate_instantiation ::=
//   pass_en_switchtype [delay2] pass_enable_switch_instance
//                      {, pass_enable_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_Tranif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Tranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_PassEnWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(3, 5) t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pass_switchtype alternative)
// gate_instantiation ::=
//   pass_switchtype pass_switch_instance {, pass_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_TranBasic) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_RtranBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (io1, io2);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.1 Production #7: pass_switch_instance
// pass_switch_instance ::= [name_of_instance] ( inout_terminal , inout_terminal
// )
// =============================================================================
TEST(ParserA301, PassSwitchInst_TranNamed) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
