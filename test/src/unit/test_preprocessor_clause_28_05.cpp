// §28.5: buf and not gates

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, BasicBufGate) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_EQ(item->gate_inst_name, "b1");
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, BasicNotGate) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  not n1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNot);
}

TEST(Parser, GateBufMultiOutput) {
  auto r = ParseWithPreprocessor("module t; buf (o1, o2, in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

}  // namespace
