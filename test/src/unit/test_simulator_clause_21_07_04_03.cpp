#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
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
class ExtendedVcdValueChangeSim : public VcdTestBase {
 protected:
  // Drives real SystemVerilog source through parse, elaboration, lowering, and
  // the scheduler, emitting an extended VCD file in the $dumpports port form
  // (SetExtendedPortNodes) and returning its contents. The port value-change
  // form of this subclause is not selected in isolation: it is chosen because
  // the source invoked $dumpports (§21.7.3.1) on real port declarations
  // (§21.7.4.2 supplies each port's integer identifier code). So the rule's
  // input -- a port whose value the simulator resolves, dumped under the port
  // form -- is built from that real dependency syntax and carried end to end,
  // rather than hand-built into a value vector.
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
};

// §21.7.4.3 (claims p-prefix / port_value / identifier_code, end to end): the
// port value-change form is not something the writer emits on its own -- it is
// selected because the source invoked $dumpports (§21.7.3.1) rather than
// $dumpvars, and the integer identifier code it carries is the one the port's
// $var declaration assigned (§21.7.4.2). Driving two scalar ports through the
// full pipeline, each assigned a known level, shows the value change produced
// by that real dependency machinery: p immediately followed by the port_value
// state character (no space), then the strength components, then the integer
// identifier code preceded by <. The 4-state scalar form (a single-character
// charset identifier such as 1!) never stands in for it.
TEST_F(ExtendedVcdValueChangeSim, ScalarPortValueChangeFormFromDumpports) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    hi = 1'b1;\n"
      "    lo = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  // Registration is in name order: hi -> code 0, lo -> code 1.
  EXPECT_NE(content.find("$var port 1 <0 hi $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 lo $end"), std::string::npos)
      << content;
  // Each value change is p<state> with the strength components and the integer
  // identifier code of its $var declaration: the driven high port at strong
  // strength (6 6), the driven low port likewise.
  EXPECT_NE(content.find("p166 <0"), std::string::npos) << content;
  EXPECT_NE(content.find("p066 <1"), std::string::npos) << content;
  // The extended file never falls back to the 4-state scalar form, where the
  // value is followed by a one-character charset identifier (1!, 0!) instead of
  // the p-prefixed port form with an integer code.
  EXPECT_EQ(content.find("1!"), std::string::npos) << content;
  EXPECT_EQ(content.find("0!"), std::string::npos) << content;
}

// §21.7.4.3 (whole-vector port_value + strength, end to end): the extended
// format has no mechanism to dump part of a vector, so a bus port's value
// change carries every bit of the port_value, most significant bit first,
// immediately after the key character p and before the two strength components
// and the identifier code. Declaring a real four-bit object, assigning it a
// known pattern, and dumping it under $dumpports shows the whole vector emitted
// by the production path, not a b-prefixed 4-state vector form.
TEST_F(ExtendedVcdValueChangeSim, WholeVectorPortValueChangeFromDumpports) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] bus;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    bus = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port [3:0] <0 bus $end"), std::string::npos)
      << content;
  // p, then all four bits msb-first (1010), then strong/strong strength, then
  // the integer identifier code.
  EXPECT_NE(content.find("p101066 <0"), std::string::npos) << content;
  // Never the 4-state b-prefixed vector form a $dumpvars file would use.
  EXPECT_EQ(content.find("b1010"), std::string::npos) << content;
}

// §21.7.4.3 (strength components, end to end): each value change carries a
// strength0 and a strength1 component, each one of the eight SystemVerilog
// strength values encoded as a digit. A driven port reports strong strength
// (6) and an undriven, high-impedance net reports highz strength (0). Building
// one driven variable and one floating net in real source and dumping them
// under $dumpports shows both strength encodings produced by the pipeline
// alongside their port_value state characters (a driven 1 and a three-state z).
TEST_F(ExtendedVcdValueChangeSim,
       StrengthComponentsFromDrivenAndFloatingPorts) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire floating;\n"
      "  logic driven;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    driven = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  // Registration is in name order: driven -> code 0, floating -> code 1.
  // The driven port: state 1 at strong/strong strength.
  EXPECT_NE(content.find("p166 <0"), std::string::npos) << content;
  // The undriven net: three-state z at highz/highz strength.
  EXPECT_NE(content.find("pz00 <1"), std::string::npos) << content;
}

// §21.7.4.3 (value-change form for a real module port, end to end): the
// identifier code a value change carries is assigned by the $var declaration of
// a port (§21.7.4.2), and the most literal source of a port is a module's port
// list. Declaring output ports in the header, driving them with continuous
// assignments, and dumping under $dumpports shows the value-change form built
// from that real port-declaration syntax: a scalar port and a bus port each
// emit p<port_value> with the strength components and the header port's integer
// identifier code, exactly as the internal-object cases do -- confirming the
// rule applies to a declared port, not only to an internal variable or net.
TEST_F(ExtendedVcdValueChangeSim, DeclaredModulePortsUseValueChangeForm) {
  auto content = RunPortVcd(
      "module t(output o, output [3:0] bus);\n"
      "  assign o = 1'b1;\n"
      "  assign bus = 4'b0110;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  // Registration is in name order: bus -> code 0, o -> code 1.
  EXPECT_NE(content.find("$var port [3:0] <0 bus $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 o $end"), std::string::npos)
      << content;
  // The bus port dumps its whole port_value (0110, msb first) with strong
  // strength and its integer code; the scalar output port likewise.
  EXPECT_NE(content.find("p011066 <0"), std::string::npos) << content;
  EXPECT_NE(content.find("p166 <1"), std::string::npos) << content;
}

// §21.7.4.3: the identifier_code of a port value change is the port's integer
// code preceded by <, the same integer used in its $var declaration
// (§21.7.4.2). Because it is an integer rather than a single printable
// character (as in the 4-state format), it is not limited to one digit: a
// design with more than ten dumped objects yields multi-digit codes. Declaring
// eleven objects in real source and driving one of them shows the production
// registration path (§21.7.4.2) assign ascending codes 0..10, and the value
// change of the eleventh carry that two-digit integer verbatim -- not a
// truncated or single-character remapping -- through the full pipeline.
TEST_F(ExtendedVcdValueChangeSim, PortIdentifierCodeIsMultiDigitInteger) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    b0 = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  // The eleventh object (name order a0..a9, b0) is assigned the two-digit code
  // 10 in its $var declaration ...
  EXPECT_NE(content.find("$var port 1 <10 b0 $end"), std::string::npos)
      << content;
  // ... and its value change carries that same two-digit integer code.
  EXPECT_NE(content.find("p166 <10"), std::string::npos) << content;
}

}  // namespace
}  // namespace delta
