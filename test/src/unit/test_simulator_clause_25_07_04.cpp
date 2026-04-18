#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

constexpr const char* kCountTargetsInterface =
    "interface simple_bus (input logic clk);\n"
    "  int targets = 0;\n"
    "  extern forkjoin task countTargets();\n"
    "  modport target(input clk, export countTargets);\n"
    "  modport initiator(input clk);\n"
    "endinterface\n";

TEST(MultipleTaskExportsSim,
     ExternForkjoinCallFansOutToEachConnectedTargetInstance) {
  SimFixture f;
  std::string src = kCountTargetsInterface;
  src +=
      "module memMod(interface a);\n"
      "  task a.countTargets();\n"
      "    a.targets++;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "  initial begin\n"
      "    sb_intf.targets = 0;\n"
      "    sb_intf.countTargets;\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{"sb_intf.targets", 2u}});
}

TEST(MultipleTaskExportsSim,
     ExternForkjoinCallWithThreeTargetsCountsAllThree) {
  SimFixture f;
  std::string src = kCountTargetsInterface;
  src +=
      "module memMod(interface a);\n"
      "  task a.countTargets();\n"
      "    a.targets++;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "  memMod mem3(sb_intf.target);\n"
      "  initial begin\n"
      "    sb_intf.targets = 0;\n"
      "    sb_intf.countTargets;\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{"sb_intf.targets", 3u}});
}

TEST(MultipleTaskExportsSim,
     DisableViaInterfaceInstanceStopsAllForkedTaskCalls) {
  SimFixture f;
  std::string src =
      "interface simple_bus (input logic clk);\n"
      "  int completions = 0;\n"
      "  extern forkjoin task Work();\n"
      "  modport target(input clk, export Work);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Work();\n"
      "    #10;\n"
      "    a.completions++;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "  initial begin\n"
      "    sb_intf.completions = 0;\n"
      "    fork\n"
      "      sb_intf.Work;\n"
      "      #1 disable sb_intf.Work;\n"
      "    join\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{"sb_intf.completions", 0u}});
}

TEST(MultipleTaskExportsSim,
     DisableViaModuleInstanceStopsOnlyThatInstancesCall) {
  SimFixture f;
  std::string src =
      "interface simple_bus (input logic clk);\n"
      "  int completions = 0;\n"
      "  extern forkjoin task Work();\n"
      "  modport target(input clk, export Work);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Work();\n"
      "    #10;\n"
      "    a.completions++;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "  initial begin\n"
      "    sb_intf.completions = 0;\n"
      "    fork\n"
      "      sb_intf.Work;\n"
      "      #1 disable mem1.a.Work;\n"
      "    join\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{"sb_intf.completions", 1u}});
}

TEST(MultipleTaskExportsSim,
     ExternForkjoinCallWithNoDefiningModuleReturnsWithNoEffect) {
  SimFixture f;
  std::string src =
      "interface simple_bus (input logic clk);\n"
      "  int observed = 0;\n"
      "  extern forkjoin task Work();\n"
      "  modport initiator(input clk);\n"
      "endinterface\n"
      "module cpuMod(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  cpuMod cpu(sb_intf.initiator);\n"
      "  initial begin\n"
      "    sb_intf.observed = 7;\n"
      "    sb_intf.Work;\n"
      "    sb_intf.observed = 8;\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, {{"sb_intf.observed", 8u}});
}

}  // namespace
