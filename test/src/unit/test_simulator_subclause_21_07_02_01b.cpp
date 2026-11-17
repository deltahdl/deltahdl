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

class VcdValueFormsFromSource : public VcdDumpFromSourceTestBase {
 protected:
  std::string Dump(const std::string& body, const std::string& steps) {
    RunSource("module t;\n" + body +
              "  initial begin\n"
              "    $dumpfile(\"forms.vcd\");\n"
              "    $dumpvars;\n" +
              steps +
              "  end\n"
              "endmodule\n");
    return DumpFile("forms.vcd");
  }

  static std::string CodeOf(const std::string& content,
                            const std::string& name) {
    for (const auto& line : AllLines(content)) {
      auto toks = Tokens(line);
      if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) {
        return toks[3];
      }
    }
    return "<not-declared>";
  }

  static std::string Checkpoint(const std::string& content,
                                const std::string& keyword) {
    auto start = content.find("\n" + keyword + "\n");
    if (start == std::string::npos) return "<no-" + keyword + ">";
    auto end = content.find("$end", start);
    return content.substr(start, end - start);
  }
};

TEST_F(VcdValueFormsFromSource,
       DISABLED_AnUnassignedRealIsWrittenInRFormAtEveryCheckpoint) {
  auto content = Dump("  real r;\n  realtime rt;\n  shortreal sr;\n",
                      "    #1 $dumpall;\n"
                      "    #1 $dumpoff;\n"
                      "    #1;\n");
  for (const char* keyword : {"$dumpvars", "$dumpall", "$dumpoff"}) {
    auto lines = AllLines(Checkpoint(content, keyword));
    for (const char* name : {"r", "rt", "sr"}) {
      EXPECT_TRUE(HasLine(lines, "r0 " + CodeOf(content, name)))
          << keyword << ' ' << name << '\n'
          << content;
    }
  }
}

TEST_F(VcdValueFormsFromSource, ANetOfAnyStrengthIsWrittenWithoutStrength) {
  auto content = Dump(
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "  wire p;\n"
      "  assign (pull0, pull1) p = 1'b0;\n"
      "  supply1 s1;\n"
      "  tri0 t0;\n",
      "    #1 $dumpall;\n"
      "    #1;\n");
  auto lines = AllLines(Checkpoint(content, "$dumpall"));
  EXPECT_TRUE(HasLine(lines, "1" + CodeOf(content, "w"))) << content;
  EXPECT_TRUE(HasLine(lines, "0" + CodeOf(content, "p"))) << content;
  EXPECT_TRUE(HasLine(lines, "1" + CodeOf(content, "s1"))) << content;
  EXPECT_TRUE(HasLine(lines, "0" + CodeOf(content, "t0"))) << content;
}

}  // namespace
