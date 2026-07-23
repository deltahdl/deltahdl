#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
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
// The simulator resolves every port to a single 4-state value and keeps no
// record of drive direction, of separate input versus output contributions, or
// of how many drivers are active. So the only characters it can select are the
// two whose §21.7.4.3.1 meaning depends on the resolved value alone: 0 ("low")
// and 1 ("high"). Every direction-dependent character (D/U/N/Z, L/H/X/T, the
// conflict resolutions A/a/B/b/C/c, the multi-driver d/u/l/h, and the
// unknown-direction three-state F) needs directional driver information the
// Variable model does not carry and is therefore unreachable here.
//
// These tests observe the writer applying those two reachable definitions
// through the production path. The state character is a function of the port's
// resolved value, and that value is produced by the pipeline, so each test
// builds the port from real source syntax and drives it through parse,
// elaboration, lowering, and the scheduler -- selecting the port form because
// the source invoked $dumpports (§21.7.3.1) on a real port declaration whose
// $var identifier code comes from §21.7.4.2 -- rather than hand-building a
// resolved value into a vector.
class ExtendedVcdStateCharacterSim : public VcdTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.SetExtended();
      vcd.SetExtendedPortNodes();
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }
    return ReadVcd();
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

// §21.7.4.3.1 applies to any dumped port, including one declared in the module
// header rather than as an internal object. Declaring an output port, driving
// it low, and dumping under $dumpports shows the "low" definition applied to a
// value resolved for a header-declared port: the port_value run is exactly "0",
// never the "1" the high definition would give.
TEST_F(ExtendedVcdStateCharacterSim,
       HeaderOutputPortSelectsZeroStateCharacter) {
  auto content = RunPortVcd(
      "module t(output o);\n"
      "  assign o = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "0") << content;
}

}  // namespace
}  // namespace delta
