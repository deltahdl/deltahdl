#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_vcd_dump_from_source.h"
#include "helpers_text_lines.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

class VcdChangeDetectionFromSource : public VcdDumpFromSourceTestBase {
 protected:
  static constexpr const char* kDumpName = "edges.vcd";

  static std::string ClockSource(const std::string& waiter) {
    return std::string(
               "module t;\n"
               "  logic clk;\n"
               "  integer n;\n"
               "  initial begin\n"
               "    clk = 1'b0;\n"
               "    n = 0;\n"
               "    $dumpfile(\"") +
           kDumpName +
           "\");\n"
           "    $dumpvars;\n"
           "    #5 clk = 1'b1;\n"
           "    #5 clk = 1'b0;\n"
           "    #5 clk = 1'b1;\n"
           "    #5 clk = 1'b0;\n"
           "  end\n" +
           waiter + "endmodule\n";
  }

  std::string ValuesRecordedFor(const std::string& src,
                                const std::string& name) {
    RunSource(src);
    std::string content = DumpFile(kDumpName);
    std::string code = IdentCodeFor(content, name);
    if (code.empty()) return "<not-declared>";
    return ScalarChanges(content, code);
  }

  uint64_t WaiterResumes() {
    Variable* var = f_.ctx.FindVariable("n");
    return var == nullptr ? UINT64_MAX : var->value.ToUint64();
  }

 private:
  static std::string IdentCodeFor(const std::string& content,
                                  const std::string& name) {
    for (const auto& line : AllLines(content)) {
      auto toks = Tokens(line);
      if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) {
        return toks[3];
      }
    }
    return std::string();
  }

  static bool IsValueCharacter(char c) {
    return c == '0' || c == '1' || c == 'x' || c == 'X' || c == 'z' || c == 'Z';
  }

  static std::string ScalarChanges(const std::string& content,
                                   const std::string& code) {
    std::string values;
    for (const auto& line : AllLines(content)) {
      if (line.size() != code.size() + 1) continue;
      if (!IsValueCharacter(line[0])) continue;
      if (line.compare(1, code.size(), code) == 0) values.push_back(line[0]);
    }
    return values;
  }
};

TEST_F(VcdChangeDetectionFromSource, ClockWaitedOnByPosedgeRecordsEveryEdge) {
  std::string values = ValuesRecordedFor(
      ClockSource("  always @(posedge clk) n = n + 1;\n"), "clk");

  EXPECT_EQ(WaiterResumes(), 2U);
  EXPECT_EQ(values, "01010");
}

TEST_F(VcdChangeDetectionFromSource, ClockWithNoWaiterRecordsEveryEdge) {
  std::string values = ValuesRecordedFor(ClockSource(""), "clk");

  EXPECT_EQ(WaiterResumes(), 0U);
  EXPECT_EQ(values, "01010");
}

TEST_F(VcdChangeDetectionFromSource, PosedgeUnderANegedgeWaitIsStillRecorded) {
  std::string values =
      ValuesRecordedFor(std::string("module t;\n"
                                    "  logic v;\n"
                                    "  integer n;\n"
                                    "  initial begin\n"
                                    "    v = 1'b1;\n"
                                    "    n = 0;\n"
                                    "    $dumpfile(\"") +
                            kDumpName +
                            "\");\n"
                            "    $dumpvars;\n"
                            "    #5 v = 1'b0;\n"
                            "    #5 v = 1'b1;\n"
                            "  end\n"
                            "  always @(negedge v) n = n + 1;\n"
                            "endmodule\n",
                        "v");

  EXPECT_EQ(WaiterResumes(), 1U);
  EXPECT_EQ(values, "101");
}

}  // namespace
