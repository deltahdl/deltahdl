#include <gtest/gtest.h>

#include <cctype>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_file_form.h"

using namespace delta;

namespace {

// §21.7 "Value change dump (VCD) files" states what a dump file is and how many
// kinds of it there are. A VCD file holds the value changes of the variables a
// design's VCD system tasks selected, it is an ASCII file carrying header
// information, variable definitions and those value changes, and two types of
// it exist: the 4-state type, representing changes in 0, 1, x and z with no
// strength information, and the extended type, representing changes in all
// states and strength information.
//
// The subclauses below §21.7 cover each task and each file format on its own.
// What is left to this file is the distinction the clause itself draws, which
// no one subclause states: the same design, dumped one way and then the other,
// produces a file whose value changes carry no strength and a file whose value
// changes carry it. The two runs differ only in which task the source calls,
// $dumpvars for the 4-state type (§21.7.1) and $dumpports for the extended one
// (§21.7.3), so a difference between the files is a difference the type made.

// The design both runs dump: one scalar taking each of the four states the
// 4-state type represents, one per time unit, so every state reaches the file
// as a value change rather than only as an initial checkpoint.
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

// A value change of the extended type, split into the parts §21.7 requires it
// to carry. `states` are the port's state characters and `strengths` the
// strength components that follow them. Both are empty for a line that is not
// a value change of that type.
struct PortValueChange {
  std::string states;
  std::string strengths;
};

// Read one line as an extended-type value change: the key character p, the
// port's state characters, two strength components, then a space and the
// identifier code. A line the form does not fit comes back empty in both parts
// rather than half-read, so a caller counting them counts only whole ones.
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

// §21.7(a): the 4-state type represents variable changes in 0, 1, x and z. The
// design drives its scalar through all four, so each reaches the file as its
// own value change. A type recording only the two known states, or collapsing x
// and z into one character, leaves one of these four lines out.
TEST_F(ValueChangeDumpFiles, FourStateTypeRepresentsZeroOneXAndZ) {
  std::string content = RunFourState();
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!")) << content;
  EXPECT_TRUE(HasLine(lines, "1!")) << content;
  EXPECT_TRUE(HasLine(lines, "x!")) << content;
  EXPECT_TRUE(HasLine(lines, "z!")) << content;
}

// §21.7(a): the 4-state type carries no strength information. Each of its value
// changes is the state character and the identifier code and nothing else, so
// no line of the file opens with the key character p that introduces the
// extended type's strength-bearing form. This is the half of the clause's
// distinction that the extended file below fails.
TEST_F(ValueChangeDumpFiles, FourStateTypeCarriesNoStrengthInformation) {
  std::string content = RunFourState();
  for (const auto& line : AllLines(content)) {
    EXPECT_TRUE(ReadPortValueChange(line).strengths.empty())
        << "4-state value change carries strength: " << line;
  }
}

// §21.7(b): the extended type represents variable changes in all states and
// strength information, so every value change it writes carries strength
// components beside the state. Counting them rather than reading their values
// states what the clause states and leaves what strength is reported to
// §21.7.4.3.2. A file whose value changes are in the 4-state form has none, and
// this is what fails when the extended type is not selected at all.
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

// §21.7: a VCD file is an ASCII file containing header information, variable
// definitions, and the value changes for all variables specified in the task
// calls. Both types are that file, so the same three parts stand in the same
// order in each. Asserting it of one type alone would leave the other free to
// write its definitions after its value changes.
TEST_F(ValueChangeDumpFiles, BothTypesAreAsciiTextInCreationOrder) {
  std::string four_state = RunFourState();
  ExpectFileIsAsciiText(four_state);
  ExpectHeaderThenDefinitionsThenValueChanges(four_state, "$var", "#1");
  std::string extended = RunExtended();
  ExpectFileIsAsciiText(extended);
  ExpectHeaderThenDefinitionsThenValueChanges(extended, "$var", "#1");
}

}  // namespace
