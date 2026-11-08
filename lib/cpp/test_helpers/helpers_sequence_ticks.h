#pragma once

#include <cstddef>
#include <string>
#include <vector>

inline std::string SequenceTickSource(const std::string& body,
                                      const std::string& drive,
                                      const std::string& prelude = "",
                                      const std::string& locals = "") {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic te1 = 0;\n"
         "  logic te2 = 0;\n"
         "  logic te3 = 0;\n"
         "  logic te4 = 0;\n"
         "  logic te5 = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         prelude + "  sequence rule;\n" + locals + "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n" +
         drive +
         "    #10 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

inline std::string DriveTicks(const std::vector<std::vector<int>>& high_at) {
  std::string drive;
  for (int tick = 1; tick <= 15; ++tick) {
    drive += "   ";
    for (size_t i = 0; i < high_at.size(); ++i) {
      bool high = false;
      for (int at : high_at[i]) high = high || at == tick;
      drive += " te" + std::to_string(i + 1) + " = " + (high ? "1" : "0") + ";";
    }
    drive += "\n    #10;\n";
  }
  return drive;
}
