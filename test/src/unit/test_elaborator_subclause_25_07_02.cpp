#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kSimpleBus =
    "interface simple_bus(input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start = 0, rdy;\n"
    "  modport target(input req, addr, mode, start, clk, output gnt, rdy, ref "
    "data, import targetRead, targetWrite);\n"
    "  modport initiator(input gnt, rdy, clk, output req, addr, mode, start, "
    "ref data, import initiatorRead, initiatorWrite);\n"
    "  task initiatorRead(input logic [7:0] raddr); addr = raddr; mode = 0; "
    "start = ~start; $display(\"%m %h at %0t\", raddr, $time); endtask\n"
    "  task targetRead; data = addr + 1; $display(\"%m %h at %0t\", data, "
    "$time); endtask\n"
    "  task initiatorWrite(input logic [7:0] waddr); addr = waddr; mode = 1; "
    "start = ~start; $display(\"%m %h at %0t\", waddr, $time); endtask\n"
    "  task targetWrite; data = addr - 1; $display(\"%m %h at %0t\", data, "
    "$time); endtask\n"
    "endinterface: simple_bus\n";

std::string UserOf(const std::string& header, const std::string& call,
                   const std::string& connection) {
  return std::string(kSimpleBus) + "module user(" + header + ");\n" +
         "  initial " + call + ";\nendmodule\n" +
         "module top;\n  logic clk = 0;\n  simple_bus sb_intf(clk);\n" +
         "  user u(" + connection + ");\nendmodule\n";
}

void ExpectRefused(const std::string& src, const std::string& task,
                   const std::string& modport) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'" + task +
                                "' is not accessible through modport '" +
                                modport + "' of interface 'simple_bus'",
                            14, "25.5"));
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ModportTaskAccess,
     ATargetModportPickedAtTheConnectionRefusesAnInitiatorTask) {
  ExpectRefused(UserOf("interface a", "a.initiatorRead(1)", "sb_intf.target"),
                "initiatorRead", "target");
  ExpectRefused(UserOf("interface a", "a.initiatorWrite(1)", "sb_intf.target"),
                "initiatorWrite", "target");
}

TEST(ModportTaskAccess, ATargetModportPickedAtTheConnectionTakesItsOwnTasks) {
  ExpectAccepted(UserOf("interface a", "a.targetRead", "sb_intf.target"));
  ExpectAccepted(UserOf("interface a", "a.targetWrite", "sb_intf.target"));
}

TEST(ModportTaskAccess,
     AnInitiatorModportPickedAtTheConnectionRefusesATargetTask) {
  ExpectRefused(UserOf("interface b", "b.targetRead", "sb_intf.initiator"),
                "targetRead", "initiator");
  ExpectRefused(UserOf("interface b", "b.targetWrite", "sb_intf.initiator"),
                "targetWrite", "initiator");
}

TEST(ModportTaskAccess,
     AnInitiatorModportPickedAtTheConnectionTakesItsOwnTasks) {
  ExpectAccepted(
      UserOf("interface b", "b.initiatorRead(1)", "sb_intf.initiator"));
  ExpectAccepted(
      UserOf("interface b", "b.initiatorWrite(1)", "sb_intf.initiator"));
}

TEST(ModportTaskAccess, AModportNamedInTheHeaderRefusesATaskItDoesNotImport) {
  ExpectRefused(UserOf("simple_bus.initiator b", "b.targetRead", "sb_intf"),
                "targetRead", "initiator");
  ExpectAccepted(
      UserOf("simple_bus.initiator b", "b.initiatorRead(1)", "sb_intf"));
}

TEST(ModportTaskAccess, TheWholeInterfaceTakesEveryTask) {
  for (const char* call : {"b.initiatorRead(1)", "b.initiatorWrite(1)",
                           "b.targetRead", "b.targetWrite"}) {
    ExpectAccepted(UserOf("interface b", call, "sb_intf"));
  }
}

}  // namespace
