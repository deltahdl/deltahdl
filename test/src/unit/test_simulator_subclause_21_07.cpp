#include <gtest/gtest.h>

#include <cctype>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_file_form.h"

using namespace delta;

namespace {

constexpr const char* kFourStateSrc =
    "module t;\n"
    "  logic a;\n"
    "  initial begin\n"
    "    $dumpvars;\n"
    "    a = 1'b0;\n"
    "    #1 a = 1'b1;\n"
    "    #1 a = 1'bx;\n"
    "    #1 a = 1'bz;\n"
    "    #1;\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kExtendedSrc =
    "module m(input a, output b);\n"
    "  assign b = a;\n"
    "endmodule\n"
    "module t;\n"
    "  logic a;\n"
    "  wire b;\n"
    "  m u(a, b);\n"
    "  initial begin\n"
    "    $dumpports(u, \"ext.vcd\");\n"
    "    a = 1'b0;\n"
    "    #1 a = 1'b1;\n"
    "    #1 a = 1'bx;\n"
    "    #1 a = 1'bz;\n"
    "    #1;\n"
    "  end\n"
    "endmodule\n";

struct PortValueChange {
  std::string states;
  std::string strengths;
};

PortValueChange ReadPortValueChange(const std::string& line) {
  if (line.size() < 5 || line[0] != 'p') return {};
  auto space = line.find(' ');
  if (space == std::string::npos || space < 4) return {};
  std::string body = line.substr(1, space - 1);
  if (body.size() < 3) return {};
  std::string strengths = body.substr(body.size() - 2);
  if (!std::isdigit(static_cast<unsigned char>(strengths[0])) ||
      !std::isdigit(static_cast<unsigned char>(strengths[1]))) {
    return {};
  }
  return {body.substr(0, body.size() - 2), strengths};
}

std::string PortCode(const std::string& content, const std::string& scope,
                     const std::string& port) {
  std::string inside;
  for (const auto& line : AllLines(content)) {
    if (line.rfind("$scope module ", 0) == 0) {
      inside = line.substr(14, line.find(' ', 14) - 14);
      continue;
    }
    if (line.rfind("$upscope", 0) == 0) inside.clear();
    if (inside != scope || line.rfind("$var port ", 0) != 0) continue;
    auto code = line.find('<');
    auto space = line.find(' ', code);
    if (code == std::string::npos || space == std::string::npos) continue;
    if (line.compare(space + 1, port.size() + 1, port + " ") == 0) {
      return line.substr(code, space - code);
    }
  }
  return "";
}

class ExtendedValueChangeDump : public VcdDumpFromSourceTestBase {
 protected:
  std::string RunExtended() {
    RunSource(kExtendedSrc);
    return DumpFile("ext.vcd");
  }
};

class ValueChangeDumpFiles : public VcdDumpRunTestBase {
 protected:
  std::string RunFourState() {
    SimFixture f;
    return RunVcdDump(f, kFourStateSrc, {.scope = "t"});
  }
};

TEST_F(ValueChangeDumpFiles, FourStateTypeRepresentsZeroOneXAndZ) {
  std::string content = RunFourState();
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!")) << content;
  EXPECT_TRUE(HasLine(lines, "1!")) << content;
  EXPECT_TRUE(HasLine(lines, "x!")) << content;
  EXPECT_TRUE(HasLine(lines, "z!")) << content;
}

TEST_F(ValueChangeDumpFiles, FourStateTypeCarriesNoStrengthInformation) {
  std::string content = RunFourState();
  for (const auto& line : AllLines(content)) {
    EXPECT_TRUE(ReadPortValueChange(line).strengths.empty())
        << "4-state value change carries strength: " << line;
  }
}

TEST_F(ExtendedValueChangeDump, EveryPortValueChangeCarriesStateAndStrength) {
  std::string content = RunExtended();
  std::string in_code = PortCode(content, "u", "a");
  std::string out_code = PortCode(content, "u", "b");
  ASSERT_FALSE(in_code.empty()) << content;
  ASSERT_FALSE(out_code.empty()) << content;
  std::string in_states;
  int out_changes = 0;
  for (const auto& line : AllLines(content)) {
    if (line.empty() || line[0] != 'p') continue;
    auto space = line.find(' ');
    if (space == std::string::npos) continue;
    std::string code = line.substr(space + 1);
    if (code != in_code && code != out_code) continue;
    PortValueChange change = ReadPortValueChange(line);
    EXPECT_FALSE(change.states.empty()) << line;
    EXPECT_EQ(change.strengths.size(), 2u) << line;
    if (code == in_code) in_states += change.states;
    if (code == out_code) ++out_changes;
  }
  EXPECT_EQ(in_states, "DUNZ") << content;
  EXPECT_EQ(out_changes, 4) << content;
}

TEST_F(ExtendedValueChangeDump, ExtendedFileIsAsciiTextInCreationOrder) {
  std::string extended = RunExtended();
  ExpectFileIsAsciiText(extended);
  ExpectHeaderThenDefinitionsThenValueChanges(extended, "$var", "#1");
}

TEST_F(ValueChangeDumpFiles, FourStateFileIsAsciiTextInCreationOrder) {
  std::string four_state = RunFourState();
  ExpectFileIsAsciiText(four_state);
  ExpectHeaderThenDefinitionsThenValueChanges(four_state, "$var", "#1");
}

}  // namespace
