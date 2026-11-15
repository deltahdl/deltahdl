#pragma once

#include <string>

inline std::string ExpectDesign(const std::string& body,
                                const std::string& declarations = "") {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, b = 0, c = 0;\n"
         "  int data = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) data <= data + 1;\n"
         "  task automatic wait_for(integer value, output bit success);\n"
         "    expect (@(posedge clk) ##[1:10] data == value) success = 1;\n"
         "      else success = 0;\n"
         "  endtask\n" +
         declarations +
         "  initial begin\n"
         "    bit ok;\n"
         "    #20;\n" +
         body +
         "  end\n"
         "  initial begin\n"
         "    #22 a = 1;\n"
         "    #10 b = 1;\n"
         "    #10 c = 1;\n"
         "    #5 a = 0;\n"
         "    #10 c = 0;\n"
         "  end\n"
         "  initial #210 $finish;\n"
         "endmodule\n";
}
