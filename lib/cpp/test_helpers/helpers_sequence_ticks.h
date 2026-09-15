#pragma once

#include <cstddef>
#include <string>
#include <vector>

// The source the §16.9 and §16.10 sequence cases share: clk rises at 5, 15,
// 25, ..., tick n at 10n-5, with te1 to te5 driven as `drive` says; a
// process counts the ticks at which the named sequence `rule`, whose body is
// `body`, reaches its end point, keeping the last such time in `last`, and
// the run finishes ten time units after the drive ends. `prelude` declares
// what stands before `rule`, other sequences among it, and `locals` the
// §16.10 local variables of `rule`, written before its clock.
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

// The drive of fourteen ticks: before each tick n, te1 to te5 are set to
// whether n is among the ticks `high_at` names for the signal, and before the
// tick after the fourteenth they are all set low, so that a signal high at
// the last tick is not read as high at the next.
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
