#include <cstdint>

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.3 (Syntax 21-29) defines the value change section of the extended VCD
// file produced by $dumpports. A port value change is
//
//   p<port_value> <0_strength_component><1_strength_component>
//   <<identifier_code>
//
// where p is the key character marking a port (no space before the port_value),
// the two strength components are SystemVerilog strength values encoded as the
// digits 0..7, and the identifier_code is the integer preceded by < that the
// port's $var declaration uses (§21.7.4.2). These tests drive the same
// VcdWriter that emits the file (the output stage), with the extended port form
// selected by SetExtendedPortNodes().
class ExtendedVcdValueChangeSim : public VcdTestBase {};

// Build a width-bit Logic4Vec from a raw value.
Logic4Vec MakeBits(Arena& arena, uint32_t width, uint64_t val) {
  return MakeLogic4VecVal(arena, width, val);
}

// Build a 1-bit Logic4Vec from raw aval/bval bits so every logic state can be
// reached: (0,0)=0, (1,0)=1, (0,1)=x, (1,1)=z.
Logic4Vec MakeScalar(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}

// §21.7.4.3: a scalar port value change has the form p<port_value><s0><s1> with
// the identifier code following. This single observation covers several of the
// clause's rules at once:
//   - the value begins with the key character p, immediately followed by the
//     port_value state character, with no space between them;
//   - all four binary port_value states (0, 1, x, z) are emitted;
//   - both strength components are present and encoded as strength-value
//   digits:
//     a driven port reports strong strength (6) and a high-impedance (z) port
//     reports highz strength (0) for both components;
//   - the identifier_code is the integer preceded by < that the port's $var
//     declaration uses, not the 4-state character identifier.
TEST_F(ExtendedVcdValueChangeSim, ScalarPortValueChangesUseExtendedForm) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* p0 = arena_.Create<Variable>();
    p0->value = MakeScalar(arena_, 0, 0);  // 0, port_id 0
    vcd.RegisterSignal("p0", 1, p0);
    auto* p1 = arena_.Create<Variable>();
    p1->value = MakeScalar(arena_, 1, 0);  // 1, port_id 1
    vcd.RegisterSignal("p1", 1, p1);
    auto* px = arena_.Create<Variable>();
    px->value = MakeScalar(arena_, 0, 1);  // x, port_id 2
    vcd.RegisterSignal("px", 1, px);
    auto* pz = arena_.Create<Variable>();
    pz->value = MakeScalar(arena_, 1, 1);  // z, port_id 3
    vcd.RegisterSignal("pz", 1, pz);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  // Each driven port: p, the binary state, strong/strong (6 6), then its
  // integer identifier code.
  EXPECT_NE(content.find("p066 <0"), std::string::npos);
  EXPECT_NE(content.find("p166 <1"), std::string::npos);
  EXPECT_NE(content.find("px66 <2"), std::string::npos);
  // The high-impedance port reports highz/highz (0 0) strength.
  EXPECT_NE(content.find("pz00 <3"), std::string::npos);
  // The value change uses the same integer identifier code as the $var
  // declaration, not the 4-state character identifier (e.g. 0! / 1").
  EXPECT_NE(content.find("$var port 1 <0 p0 $end"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
  EXPECT_EQ(content.find("1\""), std::string::npos);
}

// §21.7.4.3: the extended format has no mechanism to dump part of a vector, so
// a bus port's value change carries the whole vector — one port_value state
// character per bit, most significant bit first — followed by the strength
// components and the identifier code. This exercises the multi-bit port_value
// branch, which the scalar test does not reach.
TEST_F(ExtendedVcdValueChangeSim, WholeVectorPortValueDumpsEveryBit) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* bus = arena_.Create<Variable>();
    bus->value = MakeBits(arena_, 4, 0xA);  // 1010, port_id 0
    // input [3:0] bus -> msb 3, lsb 0.
    vcd.RegisterSignal("bus", 4, bus, NetType::kWire, 3, 0);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  // Every one of the four bits appears as its own state character, MSB first,
  // with no leading-digit shortening; then strong/strong strength and the
  // integer identifier code.
  EXPECT_NE(content.find("p101066 <0"), std::string::npos);
}

// §21.7.4.3: the identifier_code of a port value change is the port's integer
// code preceded by <, the same integer used in its $var declaration
// (§21.7.4.2). Because it is an integer rather than a single printable
// character (as in the 4-state format), it is not limited to one digit: a
// design with more than ten ports yields multi-digit codes. This edge case
// registers eleven ports so the last is assigned the two-digit code 10, and
// confirms the value change carries that integer verbatim rather than
// truncating or remapping it to one character.
TEST_F(ExtendedVcdValueChangeSim, PortIdentifierCodeIsMultiDigitInteger) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    // Eleven scalar ports each driven to 1; identifier codes ascend 0..10 in
    // registration order, so the eleventh port's code is the two-digit 10.
    const char* names[11] = {"p00", "p01", "p02", "p03", "p04", "p05",
                             "p06", "p07", "p08", "p09", "p10"};
    for (int i = 0; i < 11; ++i) {
      auto* port = arena_.Create<Variable>();
      port->value = MakeScalar(arena_, 1, 0);
      vcd.RegisterSignal(names[i], 1, port);
    }
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  // The eleventh port uses the two-digit integer identifier code in both its
  // $var declaration and its value change.
  EXPECT_NE(content.find("$var port 1 <10 p10 $end"), std::string::npos);
  EXPECT_NE(content.find("p166 <10"), std::string::npos);
}

}  // namespace
}  // namespace delta
