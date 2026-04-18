#include "fixture_parser.h"

using namespace delta;

namespace {

constexpr const char* kReadWriteInterfaceExample =
    "interface simple_bus (input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start, rdy;\n"
    "\n"
    "  modport target (input req, addr, mode, start, clk,\n"
    "                  output gnt, rdy,\n"
    "                  ref data,\n"
    "                  import targetRead,\n"
    "                         targetWrite);\n"
    "\n"
    "  modport initiator(input gnt, rdy, clk,\n"
    "                    output req, addr, mode, start,\n"
    "                    ref data,\n"
    "                    import initiatorRead,\n"
    "                           initiatorWrite);\n"
    "\n"
    "  task initiatorRead(input logic [7:0] raddr);\n"
    "  endtask\n"
    "\n"
    "  task targetRead;\n"
    "  endtask\n"
    "\n"
    "  task initiatorWrite(input logic [7:0] waddr);\n"
    "  endtask\n"
    "\n"
    "  task targetWrite;\n"
    "  endtask\n"
    "endinterface\n"
    "\n"
    "module memMod(interface a);\n"
    "  logic avail;\n"
    "  always @(posedge a.clk)\n"
    "    a.gnt <= a.req & avail;\n"
    "  always @(a.start)\n"
    "    if (a.mode[0] == 1'b0)\n"
    "      a.targetRead;\n"
    "    else\n"
    "      a.targetWrite;\n"
    "endmodule\n"
    "\n"
    "module cpuMod(interface b);\n"
    "  enum {read, write} instr;\n"
    "  logic [7:0] raddr;\n"
    "  always @(posedge b.clk)\n"
    "    if (instr == read)\n"
    "      b.initiatorRead(raddr);\n"
    "    else\n"
    "      b.initiatorWrite(raddr);\n"
    "endmodule\n"
    "\n"
    "module omniMod(interface b);\n"
    "endmodule\n"
    "\n"
    "module top;\n"
    "  logic clk = 0;\n"
    "  simple_bus sb_intf(clk);\n"
    "  memMod mem(sb_intf.target);\n"
    "  cpuMod cpu(sb_intf.initiator);\n"
    "  omniMod omni(sb_intf);\n"
    "endmodule\n";

TEST(ReadWriteInterfaceExample, ParsesFullExample) {
  auto r = Parse(kReadWriteInterfaceExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->modules.size(), 4u);
}

TEST(ReadWriteInterfaceExample, InterfaceDeclaresFourTasks) {
  auto r = Parse(kReadWriteInterfaceExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  int task_count = 0;
  bool has_initiator_read = false;
  bool has_target_read = false;
  bool has_initiator_write = false;
  bool has_target_write = false;
  for (auto* item : iface->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      ++task_count;
      if (item->name == "initiatorRead") has_initiator_read = true;
      if (item->name == "targetRead") has_target_read = true;
      if (item->name == "initiatorWrite") has_initiator_write = true;
      if (item->name == "targetWrite") has_target_write = true;
    }
  }
  EXPECT_EQ(task_count, 4);
  EXPECT_TRUE(has_initiator_read);
  EXPECT_TRUE(has_target_read);
  EXPECT_TRUE(has_initiator_write);
  EXPECT_TRUE(has_target_write);
}

TEST(ReadWriteInterfaceExample, TargetModportCombinesDirectionsAndImports) {
  auto r = Parse(kReadWriteInterfaceExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  ModportDecl* target = nullptr;
  for (auto* mp : iface->modports) {
    if (mp->name == "target") target = mp;
  }
  ASSERT_NE(target, nullptr);
  bool imports_target_read = false;
  bool imports_target_write = false;
  bool has_direction_port = false;
  for (const auto& port : target->ports) {
    if (port.is_import && port.prototype != nullptr) {
      if (port.prototype->name == "targetRead") imports_target_read = true;
      if (port.prototype->name == "targetWrite") imports_target_write = true;
    } else if (!port.is_import && !port.is_export) {
      has_direction_port = true;
    }
  }
  EXPECT_TRUE(imports_target_read);
  EXPECT_TRUE(imports_target_write);
  EXPECT_TRUE(has_direction_port);
}

TEST(ReadWriteInterfaceExample, InitiatorModportCombinesDirectionsAndImports) {
  auto r = Parse(kReadWriteInterfaceExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ModportDecl* initiator = nullptr;
  for (auto* mp : iface->modports) {
    if (mp->name == "initiator") initiator = mp;
  }
  ASSERT_NE(initiator, nullptr);
  bool imports_initiator_read = false;
  bool imports_initiator_write = false;
  bool has_direction_port = false;
  for (const auto& port : initiator->ports) {
    if (port.is_import && port.prototype != nullptr) {
      if (port.prototype->name == "initiatorRead") imports_initiator_read = true;
      if (port.prototype->name == "initiatorWrite") imports_initiator_write = true;
    } else if (!port.is_import && !port.is_export) {
      has_direction_port = true;
    }
  }
  EXPECT_TRUE(imports_initiator_read);
  EXPECT_TRUE(imports_initiator_write);
  EXPECT_TRUE(has_direction_port);
}

TEST(ReadWriteInterfaceExample, TopBindsModportSelectorsAndBareInterface) {
  auto r = Parse(kReadWriteInterfaceExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleDecl* top = nullptr;
  for (auto* m : r.cu->modules) {
    if (m->name == "top") top = m;
  }
  ASSERT_NE(top, nullptr);
  bool found_target_selector = false;
  bool found_initiator_selector = false;
  bool found_bare_binding = false;
  for (auto* item : top->items) {
    if (item->kind != ModuleItemKind::kInstance) continue;
    if (item->inst_ports.size() != 1u) continue;
    auto* conn = item->inst_ports[0].second;
    if (conn == nullptr) continue;
    if (conn->kind == ExprKind::kMemberAccess && conn->lhs != nullptr &&
        conn->rhs != nullptr && conn->lhs->text == "sb_intf") {
      if (conn->rhs->text == "target") found_target_selector = true;
      if (conn->rhs->text == "initiator") found_initiator_selector = true;
    } else if (conn->kind == ExprKind::kIdentifier &&
               conn->text == "sb_intf") {
      found_bare_binding = true;
    }
  }
  EXPECT_TRUE(found_target_selector);
  EXPECT_TRUE(found_initiator_selector);
  EXPECT_TRUE(found_bare_binding);
}

}  // namespace
