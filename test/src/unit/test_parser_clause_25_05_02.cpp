#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceModportInstantiation, InstancePortPositionalModportSelector) {
  auto r = Parse(
      "interface simple_bus;\n"
      "  logic clk;\n"
      "  modport target(input clk);\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* top = r.cu->modules.back();
  ASSERT_GE(top->items.size(), 2u);
  auto* mem = top->items[1];
  EXPECT_EQ(mem->inst_module, "memMod");
  EXPECT_EQ(mem->inst_name, "mem");
  ASSERT_EQ(mem->inst_ports.size(), 1u);
  EXPECT_EQ(mem->inst_ports[0].first, "");
  auto* conn = mem->inst_ports[0].second;
  ASSERT_NE(conn, nullptr);
  EXPECT_EQ(conn->kind, ExprKind::kMemberAccess);
  ASSERT_NE(conn->lhs, nullptr);
  EXPECT_EQ(conn->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(conn->lhs->text, "sb_intf");
  ASSERT_NE(conn->rhs, nullptr);
  EXPECT_EQ(conn->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(conn->rhs->text, "target");
}

TEST(InterfaceModportInstantiation, InstancePortNamedModportSelector) {
  auto r = Parse(
      "interface simple_bus;\n"
      "  logic clk;\n"
      "  modport initiator(output clk);\n"
      "endinterface\n"
      "module cpuMod(simple_bus b);\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  cpuMod cpu(.b(sb_intf.initiator));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* top = r.cu->modules.back();
  ASSERT_GE(top->items.size(), 2u);
  auto* cpu = top->items[1];
  ASSERT_EQ(cpu->inst_ports.size(), 1u);
  EXPECT_EQ(cpu->inst_ports[0].first, "b");
  auto* conn = cpu->inst_ports[0].second;
  ASSERT_NE(conn, nullptr);
  EXPECT_EQ(conn->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(conn->lhs->text, "sb_intf");
  EXPECT_EQ(conn->rhs->text, "initiator");
}

}  // namespace
