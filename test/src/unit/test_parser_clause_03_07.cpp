#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.7: Built-in primitives represent low-level logic gates and switches.

TEST(ParserClause03, Cl3_7_BuiltInNInputGates) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and  g1(y, a, b);\n"
      "  nand g2(y, a, b);\n"
      "  or   g3(y, a, b);\n"
      "  nor  g4(y, a, b);\n"
      "  xor  g5(y, a, b);\n"
      "  xnor g6(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 6u);
}

TEST(ParserClause03, Cl3_7_BuiltInNOutputGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, y1, y2;\n"
              "  buf  g1(y1, a);\n"
              "  not  g2(y2, a);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInEnableGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, en, y;\n"
              "  bufif0 g1(y, a, en);\n"
              "  bufif1 g2(y, a, en);\n"
              "  notif0 g3(y, a, en);\n"
              "  notif1 g4(y, a, en);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInPassGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b;\n"
              "  tran  g1(a, b);\n"
              "  rtran g2(a, b);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInPassEnableGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, en;\n"
              "  tranif0  g1(a, b, en);\n"
              "  tranif1  g2(a, b, en);\n"
              "  rtranif0 g3(a, b, en);\n"
              "  rtranif1 g4(a, b, en);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInMosSwitches) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire out, in, gate;\n"
              "  nmos  g1(out, in, gate);\n"
              "  pmos  g2(out, in, gate);\n"
              "  rnmos g3(out, in, gate);\n"
              "  rpmos g4(out, in, gate);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInCmosSwitches) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire out, in, nctrl, pctrl;\n"
              "  cmos  g1(out, in, nctrl, pctrl);\n"
              "  rcmos g2(out, in, nctrl, pctrl);\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_7_BuiltInPullGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b;\n"
              "  pullup   g1(a);\n"
              "  pulldown g2(b);\n"
              "endmodule\n"));
}

// §3.7: UDPs are enclosed between primitive...endprimitive.

TEST(ParserClause03, Cl3_7_UdpEnclosedByKeywords) {
  auto r = Parse(
      "primitive udp_buf (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_buf");
}

TEST(ParserClause03, Cl3_7_UdpInstantiationInModule) {
  auto r = Parse(
      "primitive udp_and (output out, input a, b);\n"
      "  table 0 0 : 0; 0 1 : 0; 1 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire a, b, y;\n"
      "  udp_and u1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
}

TEST(ParserClause03, Cl3_7_BuiltInAndUdpCoexist) {
  auto r = Parse(
      "primitive udp_inv (output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire a, b, y1, y2;\n"
      "  and g1(y1, a, b);\n"
      "  udp_inv u1(y2, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
}

}  // namespace
