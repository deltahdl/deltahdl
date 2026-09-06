#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.3.1 defines the meaning of each port_value state character that can
// follow the key character p in an extended-VCD value change. The clause is a
// definition table, not a grammar: the BNF that admits these characters
// (port_value ::= input_value | output_value | unknown_direction_value, with
// their alternations) is Syntax 21-27 in §21.7.4.1, and the value-change form
// that carries the character (value ::= p port_value <s0><s1>) is Syntax 21-29
// in §21.7.4.3. This subclause only assigns semantics, grouped by the direction
// the value comes from:
//   INPUT (test fixture): D low, U high, N unknown, Z three-state, and the
//     multi-driver forms d/u.
//   OUTPUT (DUT):         L low, H high, X unknown, T three-state, and the
//     multi-driver forms l/h.
//   UNKNOWN DIRECTION:    0 low (both input and output active with 0), 1 high
//     (both active with 1), ? unknown, F three-state, and the input/output
//     conflict combinations A/a/B/b/C/c/f.
//
// The simulator resolves every port to one 4-state value and does not separate
// an input contribution from an output one or count how many drivers are
// active, so the characters that describe those -- the conflict resolutions
// A/a/B/b/C/c/f and the multi-driver d/u/l/h -- are unreachable here. Which
// list the other four come from is a property of the declaration rather than of
// the resolved value, and the declared direction is recorded, so a port
// declared input reports D/U/N/Z, one declared output L/H/X/T, and an object
// no port declaration covers -- a module-body net or variable, or an inout,
// which is both ends at once -- reports 0/1/?/F.
//
// These tests observe the writer applying those two reachable definitions
// through the production path. The state character is a function of the port's
// resolved value, and that value is produced by the pipeline, so each test
// builds the port from real source syntax and drives it through parse,
// elaboration, lowering, and the scheduler -- on a real port declaration whose
// $var identifier code comes from §21.7.4.2 -- rather than hand-building a
// resolved value into a vector. The port form itself is selected by the
// fixture below, not by the source's $dumpports, because RunVcdDump installs
// its writer before the run.
class ExtendedVcdStateCharacterSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }

  // Return the run of port_value state characters in the first port value
  // change: the characters between the key character p and the two strength
  // component digits that precede the space before the identifier code.
  static std::string PortStateChars(const std::string& content) {
    size_t nl_p = content.find("\np");
    if (nl_p == std::string::npos) return "<no-value-change>";
    size_t start = nl_p + 2;  // past the newline and the key character p
    size_t space = content.find(' ', start);
    if (space == std::string::npos || space - start < 2) return "<malformed>";
    // Drop the two trailing strength-component digits.
    return content.substr(start, space - start - 2);
  }

  // The same run, taken from the value change whose identifier code is `code`
  // (§21.7.4.2) rather than from the first one in the file, so a design with
  // more than one dumped object can be asked about a named port of it.
  static std::string PortStateCharsFor(const std::string& content,
                                       const std::string& code) {
    for (const auto& line : AllLines(content)) {
      if (line.empty() || line[0] != 'p') continue;
      size_t space = line.find(' ');
      if (space == std::string::npos || space < 4) continue;
      if (line.substr(space) != " <" + code) continue;
      // Past the key character p, and short of the two strength digits.
      return line.substr(1, space - 3);
    }
    return "<no-such-record>";
  }
};

// §21.7.4.3.1: the state character 0 is defined as "low". A scalar port that
// the simulator resolves to logic 0 is reported with that character. Declaring
// a real object, driving it low, and dumping it under $dumpports shows the
// writer select 0 from the resolved value -- the value change is p0 followed by
// the strength digits and the identifier code, so the port_value run is exactly
// "0".
TEST_F(ExtendedVcdStateCharacterSim, ResolvedLowSelectsZeroStateCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic lo;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    lo = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "0") << content;
}

// §21.7.4.3.1: the state character 1 is defined as "high". A scalar port the
// simulator resolves to logic 1 is reported with that character, selected from
// the resolved value by the production writer.
TEST_F(ExtendedVcdStateCharacterSim, ResolvedHighSelectsOneStateCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic hi;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    hi = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "1") << content;
}

// §21.7.4.3.1 defines the state character per bit, and the extended format has
// no way to dump part of a vector, so every bit of a bus port contributes its
// own state character. Each resolved bit is drawn from this subclause's
// vocabulary: a mixed 0/1 pattern yields a run made only of the "low" (0) and
// "high" (1) characters, most significant bit first, matching the bit pattern.
TEST_F(ExtendedVcdStateCharacterSim, EachVectorBitSelectsAStateCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] bus;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    bus = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  // Each bit maps through §21.7.4.3.1: 1->high(1), 0->low(0), msb first.
  EXPECT_EQ(PortStateChars(content), "1010") << content;
}

// §21.7.4.3.1 selects the state character from the port's resolved value, and
// that value can be produced by a different syntactic path than a procedural
// assignment: a continuous assignment resolving a net. Driving a net high with
// assign and dumping it under $dumpports shows the same "high" definition
// applied to a value the pipeline resolved through net resolution -- the
// port_value run is exactly "1", never the "0" the low definition would give.
TEST_F(ExtendedVcdStateCharacterSim,
       ContinuousAssignedNetSelectsOneStateCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "1") << content;
}

// §21.7.4.3.1: a port declared output reports its states from the OUTPUT (DUT)
// list, where low is L. Declaring an output port in the module header, driving
// it low and dumping under $dumpports shows the direction reaching the record:
// the port_value run is exactly "L", never the "0" the unknown-direction list
// would give and never the "H" the high definition would.
TEST_F(ExtendedVcdStateCharacterSim, HeaderOutputPortLowSelectsOutputLow) {
  auto content = RunPortVcd(
      "module t(output o);\n"
      "  assign o = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "L") << content;
}

// §21.7.4.3.1: the same port at the other value takes the same list's H. Low
// alone would be satisfied by a mapping that answered L for everything.
TEST_F(ExtendedVcdStateCharacterSim, HeaderOutputPortHighSelectsOutputHigh) {
  auto content = RunPortVcd(
      "module t(output o);\n"
      "  assign o = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "H") << content;
}

// §21.7.4.3.1: a port declared input reports from the INPUT (TESTFIXTURE)
// list, where high is U. An input is driven from outside the module it belongs
// to, so the design instantiates the module and drives the connection. The
// INPUT and OUTPUT lists are disjoint, so an output case cannot stand for this
// one. Registration is in name order, giving a code 0 and k1.i code 1.
TEST_F(ExtendedVcdStateCharacterSim, InputPortHighSelectsInputHigh) {
  auto content = RunPortVcd(
      "module s(input i);\n"
      "endmodule\n"
      "module t;\n"
      "  logic a;\n"
      "  s k1(.i(a));\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    $dumpports;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortStateCharsFor(content, "1"), "U") << content;
  // The object driving it is no port and faces no way, so it keeps the
  // unknown-direction list's 1 -- the two lists are being told apart in one
  // file.
  EXPECT_EQ(PortStateCharsFor(content, "0"), "1") << content;
}

// §21.7.4.3.1: an unknown value on an object of unknown direction is ?. The
// 4-state character x belongs to no one of the three lists, so this is the case
// that was outside the alphabet rather than merely ambiguous about direction.
TEST_F(ExtendedVcdStateCharacterSim, UnknownValueSelectsTheUnknownCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic u;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    u = 1'bx;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "?") << content;
}

}  // namespace
}  // namespace delta
