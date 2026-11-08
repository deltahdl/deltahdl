#include <gtest/gtest.h>

#include <cctype>
#include <string>

#include "fixture_simulator.h"
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
    "module t;\n"
    "  logic a;\n"
    "  initial begin\n"
    "    $dumpports;\n"
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

class ValueChangeDumpFiles : public VcdDumpRunTestBase {
 protected:
  std::string RunFourState() {
    SimFixture f;
    return RunVcdDump(f, kFourStateSrc, {.scope = "t"});
  }

  std::string RunExtended() {
    SimFixture f;
    return RunVcdDump(f, kExtendedSrc, {.scope = "t", .extended = true});
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

TEST_F(ValueChangeDumpFiles, ExtendedTypeCarriesStrengthWithEveryValueChange) {
  std::string content = RunExtended();
  int with_strength = 0;
  for (const auto& line : AllLines(content)) {
    if (line.empty() || line[0] != 'p') continue;
    PortValueChange change = ReadPortValueChange(line);
    EXPECT_FALSE(change.states.empty()) << line;
    EXPECT_EQ(change.strengths.size(), 2u) << line;
    ++with_strength;
  }
  EXPECT_GE(with_strength, 3) << content;
}

TEST_F(ValueChangeDumpFiles, BothTypesAreAsciiTextInCreationOrder) {
  std::string four_state = RunFourState();
  ExpectFileIsAsciiText(four_state);
  ExpectHeaderThenDefinitionsThenValueChanges(four_state, "$var", "#1");
  std::string extended = RunExtended();
  ExpectFileIsAsciiText(extended);
  ExpectHeaderThenDefinitionsThenValueChanges(extended, "$var", "#1");
}

}  // namespace
