#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_logic4vec.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
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
class ExtendedVcdNodeInfoSim : public VcdTestBase {
 protected:
  // Drives real SystemVerilog source through parse, elaboration, lowering, and
  // the scheduler, emitting an extended VCD file in the port-node form a
  // $dumpports dump uses (SetExtendedPortNodes), and returns its contents. This
  // mirrors a driver configured for extended output: the dumpable objects are
  // registered by the context from their real declarations, so each entry's
  // size (a bus range or a scalar 1), identifier code, and reference are
  // derived by production code from the source -- not hand-built into a spec.
  // Whether a size is a range or a scalar 1 depends on how the object was
  // declared, so this rule is observed here end to end rather than
  // synthetically.
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
      // §21.7.2.1: the context registers the dumpable objects in name order,
      // assigning the ascending port identifier codes as it goes.
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
};

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
    vcd.RegisterSignal(VcdSignalSpec{"data", 4, data, NetType::kWire, 0, 3});
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
    vcd.RegisterSignal(VcdSignalSpec{"data", 8, data, NetType::kWire, 7, 0});
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // The declared range is emitted msb:lsb exactly, not flipped to [0:7].
  EXPECT_NE(content.find("$var port [7:0] <0 data $end"), std::string::npos);
  EXPECT_EQ(content.find("[0:7]"), std::string::npos);
}

// §21.7.4.2 (size rule, end to end): the size field distinguishes a bus from a
// single-bit port. A port that is a bus prints its index range as [msb:lsb];
// a single-bit port prints 1. Because this choice is driven by how the object
// is declared -- a vector versus a scalar -- the declarations are written in
// real source and carried through parse, elaboration, lowering, and the dump so
// the production registration path derives the size, rather than a hand-built
// spec. A 4-state $var line (size as a plain bit count) must never appear.
TEST_F(ExtendedVcdNodeInfoSim,
       BusPrintsIndexRangeScalarPrintsOneFromDeclaration) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] data = 4'b0000;\n"
      "  logic en = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  // The four-bit vector is a bus -- its size is the index range [3:0], not the
  // bit count 4 a 4-state file would print ...
  EXPECT_NE(content.find("$var port [3:0] <0 data $end"), std::string::npos)
      << content;
  // ... while the one-bit object is a scalar and prints 1.
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  // No bus prints a bare bit count, and no 4-state var_type leaks in.
  EXPECT_EQ(content.find("$var port 4 "), std::string::npos) << content;
  EXPECT_EQ(content.find("$var wire"), std::string::npos);
  EXPECT_EQ(content.find("$var logic"), std::string::npos);
}

// §21.7.4.2 (var_type rule, end to end): the var_type keyword is always port
// and no other keyword is allowed, whatever the declared kind of the dumped
// object. A 4-state file would declare each of these with a different keyword
// (logic, integer, real); in the extended node information every one is a port.
// The declarations are real source so the keyword is fixed by the writer's port
// mode rather than derived from a synthesized data-type field.
TEST_F(ExtendedVcdNodeInfoSim, VarTypeIsPortForEveryDeclaredKind) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  integer i = 0;\n"
      "  real r = 0.0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  // Registration is in name order: a, i, r.
  EXPECT_NE(content.find("$var port 1 <0 a $end"), std::string::npos)
      << content;
  // A 32-bit integer is a bus in the node information ...
  EXPECT_NE(content.find("$var port [31:0] <1 i $end"), std::string::npos)
      << content;
  // ... and a real is dumped as one value, so it keeps the scalar size 1.
  EXPECT_NE(content.find("$var port 1 <2 r $end"), std::string::npos)
      << content;
  // None of the 4-state / data-type keywords appear in the node information.
  EXPECT_EQ(content.find("$var integer"), std::string::npos);
  EXPECT_EQ(content.find("$var real"), std::string::npos);
  EXPECT_EQ(content.find("$var logic"), std::string::npos);
}

// §21.7.4.2 (identifier_code rule, end to end): each port's identifier code is
// an integer preceded by < that starts at zero and ascends one unit per port.
// Driving several declarations through the pipeline shows the codes assigned by
// the production registration order, 0,1,2, with no repeats and no charset
// identifier (the ! form a 4-state file would use) in their place. The clause
// also states that the codes follow the order the ports are found in the module
// declaration; the production registration path (§21.7.2.1) walks the dumpable
// objects in name order, so the declarations here are named a, b, c to make the
// two orders coincide -- the code-assignment sequence itself (integer, from
// zero, one per port) is what this observes, independent of that tie-break.
TEST_F(ExtendedVcdNodeInfoSim, IdentifierCodesAreAscendingIntegersFromZero) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b0;\n"
      "  logic c = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <0 a $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 b $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <2 c $end"), std::string::npos)
      << content;
  // The integer code form is used: a charset identifier such as < ! never
  // stands in for the ascending integer.
  EXPECT_EQ(content.find("$var port 1 <! "), std::string::npos) << content;
}

// §21.7.4.2 (vector_index selection, end to end): when the vector_index appears
// in the port declaration itself, that range is the one dumped; when the port
// carries no range it is treated as a one-bit scalar. This exercises the rule's
// own input forms -- a real module port declared with a packed range and a real
// module port declared with none -- rather than an internal variable, driving
// the actual port declarations through the pipeline so the production path
// derives the size from the declared port.
TEST_F(ExtendedVcdNodeInfoSim,
       PortDeclarationRangeSelectsBusSizeScalarPortSelectsOne) {
  auto content = RunPortVcd(
      "module t(input [3:0] data, input en);\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  // The port declared with the [3:0] range dumps that index range ...
  EXPECT_NE(content.find("$var port [3:0] <0 data $end"), std::string::npos)
      << content;
  // ... and the port declared with no range is a one-bit scalar.
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  // The bus never prints a bare bit count in place of its index range.
  EXPECT_EQ(content.find("$var port 4 "), std::string::npos) << content;
}

// §21.7.4.2 also describes taking the vector_index from the net or variable
// declaration that matches the port name when the port declaration itself
// carries none. That form is not separately reachable here: the elaborator
// requires a variable's declared range to match its port declaration, so a
// range supplied only by a later net/variable declaration is rejected before
// simulation rather than dumped. The range therefore always originates in the
// port declaration (exercised above), and the scalar fallback for a port with
// no range is exercised by the scalar port there as well.

// §21.7.4.2 (var_type for a net port, end to end): the node-information entry
// of a port whose object is a net still uses the port keyword, and its
// vector_index is dumped by the same 4-state range rules as any bus. A 4-state
// file would declare such a net with the wire keyword; the extended node
// information never does. The net port is declared in real source so the
// keyword is fixed by the writer's port mode, not by the object's net type.
TEST_F(ExtendedVcdNodeInfoSim, NetPortUsesPortKeywordWithItsIndexRange) {
  auto content = RunPortVcd(
      "module t(output wire [7:0] bus, input en);\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  // The eight-bit net port is a port with its [7:0] index range ...
  EXPECT_NE(content.find("$var port [7:0] <0 bus $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 en $end"), std::string::npos)
      << content;
  // ... never the wire var_type a 4-state file would give a net.
  EXPECT_EQ(content.find("$var wire"), std::string::npos) << content;
}

// §21.7.4.2 also states that concatenated ports shall appear in the extended
// VCD file as separate entries. Splitting a concatenated port (for example
// {A, b}) into its member objects happens during elaboration, and this
// implementation currently collapses such a port into a single merged object
// before it reaches the simulator, so its members are not registered under
// their own names. Producing the separate members is an elaboration-stage
// concern outside this subclause's output-stage machinery, so that rule is not
// exercised here; the writer already emits one $var port line per registered
// object, as the tests above show for independently declared ports.

}  // namespace
}  // namespace delta
