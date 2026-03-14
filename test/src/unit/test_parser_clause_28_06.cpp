#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveInstantiationParsing, GateInst_Bufif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Notif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Notif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, EnableGateInst_Unnamed) {
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

TEST(PrimitiveInstantiationParsing, EnableGateInst_Named) {
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

TEST(PrimitiveInstantiationParsing, GateInst_AllEnableGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 b0(o, i, c);\n"
              "  bufif1 b1(o, i, c);\n"
              "  notif0 n0(o, i, c);\n"
              "  notif1 n1(o, i, c);\n"
              "endmodule\n"));
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif1) {
  auto r = Parse(
      "module m;\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

}  // namespace
