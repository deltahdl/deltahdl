#pragma once

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

inline std::string PathTransitionRun(const std::string& delay) {
  SimFixture f;
  return RunCapture(
      "module drv(input [1:0] s, output y);\n"
      "  assign y = s == 0 ? 1'b0 : s == 1 ? 1'b1 : s == 2 ? 1'bz : 1'bx;\n"
      "  specify\n"
      "    (s *> y) = " +
          delay +
          ";\n"
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic [1:0] s;\n"
          "  wire y;\n"
          "  drv u(.s(s), .y(y));\n"
          "  always @(y) if ($time > 0) $write(\"%0d%b \", $time % 100, y);\n"
          "  initial begin\n"
          "    s = 0;\n"
          "    #100 s = 1; #100 s = 0; #100 s = 2; #100 s = 1;\n"
          "    #100 s = 2; #100 s = 0; #100 s = 3; #100 s = 1;\n"
          "    #100 s = 3; #100 s = 0; #100 s = 3; #100 s = 2;\n"
          "    #100 s = 3; #100 $display;\n"
          "  end\n"
          "endmodule\n",
      f);
}

inline std::string BufferPathRun(const std::string& module_decls,
                                 const std::string& specify_decls,
                                 const std::string& delay, DelayMode mode) {
  SimFixture f;
  f.ctx.SetDelayMode(mode);
  return RunCapture(
      "module mybuf(input a, output y);\n"
      "  assign y = a;\n" +
          module_decls + "  specify\n" + specify_decls +
          "    (a => y) = " + delay +
          ";\n"
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic a;\n"
          "  wire y;\n"
          "  mybuf u(.a(a), .y(y));\n"
          "  always @(y) if ($time > 0)\n"
          "    $write(\"%0d%b \", $time % 100, y);\n"
          "  initial begin\n"
          "    a = 0;\n"
          "    #100 a = 1;\n"
          "    #100 a = 0;\n"
          "    #100 $display;\n"
          "  end\n"
          "endmodule\n",
      f);
}
