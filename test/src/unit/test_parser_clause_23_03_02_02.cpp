#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FormalSyntaxParsing, ModuleInstNamed) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

TEST(ModuleInstantiationGrammar, NamedPortEmptyExpression) {
  auto r = Parse("module m; sub u0(.clk(clk), .nc()); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[1].first, "nc");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(ModuleInstantiationGrammar, ElaborationModuleInstPortBinding) {
  auto r = Parse(
      "module child(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module parent;\n"
      "  wire x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 2u);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "child");
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_EQ(inst->inst_ports.size(), 2u);
}

TEST(SchedulingSemanticsParsing, NamedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.clk(clk), .rst(rst), .d(data));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "d");
}

TEST(ModuleAndHierarchyParsing, ModuleInstBasic) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.a(w1), .b(w2));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
  ASSERT_EQ(item->inst_ports.size(), 2u);
}

TEST(ModuleAndHierarchyParsing, PortConnectionNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.clk(sys_clk), .rst(sys_rst), .data(bus));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "data");
}

TEST(ModuleAndHierarchyParsing, PortConnectionEmptyNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.clk(sys_clk), .unused());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[1].first, "unused");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

TEST(ModuleAndHierarchyParsing, SimpleModuleInstance) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
}

TEST(ModuleAndHierarchyParsing, NamedPortConnectionsOrder) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.b(y), .a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "b");
  EXPECT_EQ(item->inst_ports[1].first, "a");
}

TEST(ModuleAndHierarchyParsing, NamedPortEmptyConnection) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(x), .b());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

TEST(ModuleAndHierarchyParsing, PortConnectionRulesNamedMultiple) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.clk(clk), .rst(rst), .data(d), .out(q));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 4);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "data");
  EXPECT_EQ(item->inst_ports[3].first, "out");
}

TEST(ModuleAndHierarchyParsing, PortConnectionAllEmpty) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(), .b(), .c());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->inst_ports[i].second, nullptr);
  }
}

TEST(ModuleAndHierarchyParsing, NamedPortWithPartSelect) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(bus[7:0]), .b(bus[15:8]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

TEST(ModuleAndHierarchyParsing, NamedPortWithConcatenation) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.data({a, b, c}));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "data");
  ASSERT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[0].second->kind, ExprKind::kConcatenation);
}

TEST(AttributeParserParsing, Attribute_OnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

TEST(PortConnections, NamedPortConnections) {
  auto r = Parse(
      "module sub(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  sub u0(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_FALSE(inst->inst_ports.empty());
}

}  // namespace
