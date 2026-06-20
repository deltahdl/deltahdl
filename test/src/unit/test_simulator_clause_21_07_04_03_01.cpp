#include <cstdint>
#include <string>

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.3.1 defines the vocabulary of the port_value state character that
// follows the key character p in an extended-VCD value change (the production
// value ::= p port_value <s0><s1> is Syntax 21-29, owned by the parent
// §21.7.4.3). The state characters are grouped by the direction the value comes
// from: input values from a test fixture (D, U, N, Z, d, u), output values of
// the device under test (L, H, X, T, l, h), and states whose direction is
// unknown (0, 1, ?, F, A, a, B, b, C, c, f).
//
// The simulator resolves a port to a single 4-state Logic4Vec value with no
// record of drive direction, of the separate input/output contributions, or of
// how many drivers are active. So the only state characters it can produce are
// the two that depend on the resolved value alone: 0, defined here as "low,
// both input and output active with 0 value", and 1, "high, both input and
// output active with 1 value". The direction-dependent characters (D/U/L/H,
// the conflict resolutions A/B/C, the multi-driver d/u/l/h, and the three-state
// forms Z/T/F) require directional driver information the Variable model does
// not carry and are deferred. These tests observe the writer applying the two
// reachable definitions; the extended port form is selected, as in §21.7.4.3,
// with SetExtendedPortNodes().
class ExtendedVcdStateCharacterSim : public VcdTestBase {};

// Build a 1-bit Logic4Vec from raw aval/bval bits.
Logic4Vec MakeScalarState(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}

// Return the run of port_value state characters in the first value change,
// i.e. the characters between the leading p and the two strength digits that
// precede the space and identifier code.
std::string PortValueChars(const std::string& content) {
  size_t p = content.find("\np");
  if (p == std::string::npos) return "";
  size_t start = p + 2;  // skip newline and the key character p
  size_t space = content.find(' ', start);
  if (space == std::string::npos || space - start < 2) return "";
  // The last two characters before the space are the strength components.
  return content.substr(start, space - start - 2);
}

// §21.7.4.3.1: a port resolved to logic 0 is reported with the state character
// 0 ("low, both input and output active with 0 value"). The writer selects
// that character from the resolved value, so the value change after p begins
// with 0.
TEST_F(ExtendedVcdStateCharacterSim, LowPortUsesZeroStateCharacter) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* low = arena_.Create<Variable>();
    low->value = MakeScalarState(arena_, 0, 0);
    vcd.RegisterSignal("low", 1, low);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_EQ(PortValueChars(content), "0");
}

// §21.7.4.3.1: a port resolved to logic 1 is reported with the state character
// 1 ("high, both input and output active with 1 value").
TEST_F(ExtendedVcdStateCharacterSim, HighPortUsesOneStateCharacter) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* high = arena_.Create<Variable>();
    high->value = MakeScalarState(arena_, 1, 0);
    vcd.RegisterSignal("high", 1, high);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_EQ(PortValueChars(content), "1");
}

}  // namespace
}  // namespace delta
