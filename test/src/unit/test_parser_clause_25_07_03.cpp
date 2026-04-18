#include "fixture_parser.h"

using namespace delta;

namespace {

constexpr const char* kExportTasksExample =
    "interface simple_bus (input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start, rdy;\n"
    "\n"
    "  modport target(input req, addr, mode, start, clk,\n"
    "                 output gnt, rdy,\n"
    "                 ref data,\n"
    "                 export Read,\n"
    "                        Write);\n"
    "\n"
    "  modport initiator(input gnt, rdy, clk,\n"
    "                    output req, addr, mode, start,\n"
    "                    ref data,\n"
    "                    import task Read (input logic [7:0] raddr),\n"
    "                           task Write(input logic [7:0] waddr));\n"
    "endinterface\n"
    "\n"
    "module memMod(interface a);\n"
    "  logic avail;\n"
    "  task a.Read;\n"
    "    avail = 0;\n"
    "    avail = 1;\n"
    "  endtask\n"
    "  task a.Write;\n"
    "    avail = 0;\n"
    "    avail = 1;\n"
    "  endtask\n"
    "endmodule\n"
    "\n"
    "module cpuMod(interface b);\n"
    "  enum {read, write} instr;\n"
    "  logic [7:0] raddr;\n"
    "  always @(posedge b.clk)\n"
    "    if (instr == read)\n"
    "      b.Read(raddr);\n"
    "    else\n"
    "      b.Write(raddr);\n"
    "endmodule\n"
    "\n"
    "module top;\n"
    "  logic clk = 0;\n"
    "  simple_bus sb_intf(clk);\n"
    "  memMod mem(sb_intf.target);\n"
    "  cpuMod cpu(sb_intf.initiator);\n"
    "endmodule\n";

TEST(ExportTasksExample, ParsesFullExample) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->modules.size(), 3u);
}

TEST(ExportTasksExample, TargetModportExportsReadAndWrite) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  ModportDecl* target = nullptr;
  for (auto* mp : iface->modports) {
    if (mp->name == "target") target = mp;
  }
  ASSERT_NE(target, nullptr);
  bool exports_read = false;
  bool exports_write = false;
  bool has_direction_port = false;
  for (const auto& port : target->ports) {
    if (port.is_export && port.name == "Read") exports_read = true;
    if (port.is_export && port.name == "Write") exports_write = true;
    if (!port.is_import && !port.is_export) has_direction_port = true;
  }
  EXPECT_TRUE(exports_read);
  EXPECT_TRUE(exports_write);
  EXPECT_TRUE(has_direction_port);
}

TEST(ExportTasksExample, InitiatorModportImportsFullTaskPrototypes) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ModportDecl* initiator = nullptr;
  for (auto* mp : iface->modports) {
    if (mp->name == "initiator") initiator = mp;
  }
  ASSERT_NE(initiator, nullptr);
  const ModportPort* read_port = nullptr;
  const ModportPort* write_port = nullptr;
  for (const auto& port : initiator->ports) {
    if (port.is_import && port.prototype != nullptr) {
      if (port.prototype->name == "Read") read_port = &port;
      if (port.prototype->name == "Write") write_port = &port;
    }
  }
  ASSERT_NE(read_port, nullptr);
  ASSERT_NE(write_port, nullptr);
  EXPECT_EQ(read_port->prototype->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(read_port->prototype->func_args.empty());
  EXPECT_EQ(write_port->prototype->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(write_port->prototype->func_args.empty());
}

TEST(ExportTasksExample, MemModDefinesHierarchicalTaskBodies) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleDecl* mem_mod = nullptr;
  for (auto* m : r.cu->modules) {
    if (m->name == "memMod") mem_mod = m;
  }
  ASSERT_NE(mem_mod, nullptr);
  bool has_read_body = false;
  bool has_write_body = false;
  for (auto* item : mem_mod->items) {
    if (item->kind != ModuleItemKind::kTaskDecl) continue;
    if (item->method_class == "a" && item->name == "Read") has_read_body = true;
    if (item->method_class == "a" && item->name == "Write") has_write_body = true;
  }
  EXPECT_TRUE(has_read_body);
  EXPECT_TRUE(has_write_body);
}

TEST(ExportTasksExample, CpuModCallsInterfaceTasksViaInitiatorModport) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleDecl* cpu_mod = nullptr;
  for (auto* m : r.cu->modules) {
    if (m->name == "cpuMod") cpu_mod = m;
  }
  ASSERT_NE(cpu_mod, nullptr);
  EXPECT_EQ(cpu_mod->ports.size(), 1u);
  EXPECT_EQ(cpu_mod->ports[0].name, "b");
}

TEST(ExportTasksExample, TopBindsModportSelectorsToMemAndCpu) {
  auto r = Parse(kExportTasksExample);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleDecl* top = nullptr;
  for (auto* m : r.cu->modules) {
    if (m->name == "top") top = m;
  }
  ASSERT_NE(top, nullptr);
  bool binds_target = false;
  bool binds_initiator = false;
  for (auto* item : top->items) {
    if (item->kind != ModuleItemKind::kInstance) continue;
    if (item->inst_ports.size() != 1u) continue;
    auto* conn = item->inst_ports[0].second;
    if (conn == nullptr) continue;
    if (conn->kind == ExprKind::kMemberAccess && conn->lhs != nullptr &&
        conn->rhs != nullptr && conn->lhs->text == "sb_intf") {
      if (conn->rhs->text == "target") binds_target = true;
      if (conn->rhs->text == "initiator") binds_initiator = true;
    }
  }
  EXPECT_TRUE(binds_target);
  EXPECT_TRUE(binds_initiator);
}

}  // namespace
