// §23.3.2.4: Connecting module instances using wildcard named port connections ( .*)

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA0411, WildcardPortConnection) {
  // . * — wildcard port connection
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ParserAnnexA0411, WildcardWithNamedPorts) {
  // Named ports mixed with .*
  auto r = Parse("module m; sub u0(.clk(clk), .*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(ParserAnnexA0411, ElaborationWildcardPortConnection) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b;\n"
      "  sub u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_EQ(inst->inst_ports.size(), 0u);
}

// --- interface_instantiation: wildcard port ---
TEST(ParserAnnexA0412, InterfaceInstWildcardPort) {
  auto r = Parse("module m; my_if u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- program_instantiation: wildcard port ---
TEST(ParserAnnexA0413, ProgramInstWildcardPort) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

}  // namespace
