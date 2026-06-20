#include <cstdint>
#include <cstring>

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.2 (Syntax 21-28) defines the node information (variable definitions)
// section of the extended VCD file produced by $dumpports. Each port is
// declared as
//
//   $var port <size> <<identifier_code> <reference> $end
//
// where the var_type keyword is always port, the size is the declared index
// range of a bus or 1 for a single-bit port, and the identifier_code is an
// integer preceded by < that ascends from zero in declaration order. These
// tests drive the same VcdWriter that emits the file (the output stage), with
// the extended port-node form selected by SetExtendedPortNodes().
class ExtendedVcdNodeInfoSim : public VcdTestBase {};

// Build a width-bit Logic4Vec from a raw value, mirroring how the evaluator
// stores a port's resolved value.
Logic4Vec MakeBits(Arena& arena, uint32_t width, uint64_t val) {
  return MakeLogic4VecVal(arena, width, val);
}

// §21.7.4.2: reproduces the LRM's worked node-information example. The module
//   module test_device(count_out, carry, data, reset);
//     output count_out, carry;
//     input  [0:3] data;
//     input  reset;
// dumped with $dumpports produces one $var port entry per port. This single
// observation covers several of the clause's rules at once:
//   - var_type is the keyword port for every entry, never a 4-state keyword
//     such as wire (the "no other keyword is allowed" rule);
//   - the size is 1 for the single-bit ports and the declared index range
//     [0:3] for the bus, not a plain bit count;
//   - the identifier codes are integers preceded by < that ascend 0,1,2,3 in
//     declaration order;
//   - at least one space separates each syntactical element of a declaration.
TEST_F(ExtendedVcdNodeInfoSim, MatchesNodeInformationExample) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("testbench.DUT");
    auto* count_out = arena_.Create<Variable>();
    count_out->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("count_out", 1, count_out);
    auto* carry = arena_.Create<Variable>();
    carry->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("carry", 1, carry);
    auto* data = arena_.Create<Variable>();
    data->value = MakeBits(arena_, 4, 0);
    // input [0:3] data -> msb 0, lsb 3.
    vcd.RegisterSignal("data", 4, data, NetType::kWire, 0, 3);
    auto* reset = arena_.Create<Variable>();
    reset->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("reset", 1, reset);
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // Each port is declared with the port keyword, ascending integer identifier
  // codes, and the correct size form (1 for scalars, [0:3] for the bus).
  EXPECT_NE(content.find("$var port 1 <0 count_out $end"), std::string::npos);
  EXPECT_NE(content.find("$var port 1 <1 carry $end"), std::string::npos);
  EXPECT_NE(content.find("$var port [0:3] <2 data $end"), std::string::npos);
  EXPECT_NE(content.find("$var port 1 <3 reset $end"), std::string::npos);
  // No 4-state var_type keyword leaks into the extended node information, and
  // no charset identifier code is used in place of the integer codes.
  EXPECT_EQ(content.find("$var wire"), std::string::npos);
}

// §21.7.4.2: for a bus the size field prints the declared index range with the
// most significant index first and the least significant index second. A port
// declared high-to-low (for example input [7:0] data) is recorded as [7:0] in
// that declaration order; the writer does not reorder the bounds into a
// low-to-high form. The clause's own worked example uses the ascending [0:3]
// form, so this exercises the opposite, and far more common, ordering and
// guards against the indices being normalized.
TEST_F(ExtendedVcdNodeInfoSim, BusIndexRangePreservesDeclaredMsbLsbOrder) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* data = arena_.Create<Variable>();
    data->value = MakeBits(arena_, 8, 0);
    // input [7:0] data -> msb 7, lsb 0.
    vcd.RegisterSignal("data", 8, data, NetType::kWire, 7, 0);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // The declared range is emitted msb:lsb exactly, not flipped to [0:7].
  EXPECT_NE(content.find("$var port [7:0] <0 data $end"), std::string::npos);
  EXPECT_EQ(content.find("[0:7]"), std::string::npos);
}

// §21.7.4.2: the var_type of a node-information entry is the keyword port and
// no other keyword is allowed. The acid test is a real-valued port: a 4-state
// writer declares a real object with the real keyword, but in the extended
// node information the entry is still a port. This confirms the keyword is
// fixed at port rather than derived from the dumped object's type.
TEST_F(ExtendedVcdNodeInfoSim, VarTypeIsAlwaysPortKeyword) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* freq = arena_.Create<Variable>();
    // Store the IEEE Std 754 bit pattern of a real number the way the evaluator
    // records a real result, and mark the value as real.
    uint64_t bits = 0;
    double d = 1.5;
    std::memcpy(&bits, &d, sizeof(double));
    freq->value = MakeLogic4VecVal(arena_, 64, bits);
    freq->value.is_real = true;
    vcd.RegisterSignal("freq", 64, freq);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // The real-valued port is declared with the port keyword ...
  EXPECT_NE(content.find("$var port 1 <0 freq $end"), std::string::npos);
  // ... and never with the real var_type keyword a 4-state writer would use.
  EXPECT_EQ(content.find("$var real"), std::string::npos);
}

}  // namespace
}  // namespace delta
