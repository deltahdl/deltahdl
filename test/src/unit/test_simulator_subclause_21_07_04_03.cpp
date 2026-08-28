#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
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
class ExtendedVcdValueChangeSim : public VcdDumpRunTestBase {
 protected:
  // Drives real SystemVerilog source through parse, elaboration, lowering, and
  // the scheduler, emitting an extended VCD file in the $dumpports port form
  // (SetExtendedPortNodes) and returning its contents. The form is selected by
  // this fixture rather than by the source: RunVcdDump installs its own writer
  // before the run and SimContext::OpenVcdDump returns an installed writer
  // untouched, so the source's $dumpports cannot reach the choice here. What
  // the source supplies is the rest of the input -- real port declarations
  // (§21.7.4.2 supplies each port's integer identifier code) whose values the
  // simulator resolves -- carried end to end rather than hand-built into a
  // value vector. That the task selects the form is asserted by
  // ExtendedVcdFormatChosenByTheSource in
  // test_simulator_subclause_21_07_04.cpp, which supplies no writer.
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }
};

// §21.7.4.3 (claims p-prefix / port_value / identifier_code, end to end): the
// port value-change form is selected by the fixture above, and the integer
// identifier code the record carries is the one the port's $var declaration
// assigned (§21.7.4.2), which is what this case is about. Driving two scalar
// ports through the full pipeline, each assigned a known level, shows the value
// change produced by that real dependency machinery: p immediately followed by
// the port_value state character (no space), then the strength components, then
// the integer identifier code preceded by <. The 4-state scalar form (a
// single-character charset identifier such as 1!) never stands in for it.
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

// §21.7.4.3 again, on the two strength components rather than on the p
// prefix, the port_value or the identifier code the cases above read. The
// clause defines 0_strength_component as "one of the eight SystemVerilog
// strengths that indicates the strength0 specification for the port" and
// 1_strength_component as the strength1 one, and numbers the eight 0 highz,
// 1 small, 2 medium, 3 weak, 4 large, 5 pull, 6 strong, 7 supply. §21.7 gives
// the extended file the job of representing variable changes "in all states
// and strength information", so those two digits are the whole of what the
// extended file adds over the 4-state one.
//
// Every source below drives its net at a strength other than strong, because
// a strongly driven net reports the strong digit whether the writer resolves
// the strength or assumes it. §28.6 gives a driver written with no
// drive_strength specification strong0 and strong1, so plain procedural and
// continuous assignment -- what every case above uses -- is the one input
// that cannot tell the two apart.
//
// The source selects the extended form here, as it does in
// ExtendedVcdFormatChosenByTheSource in
// test_simulator_subclause_21_07_04.cpp: VcdDumpFromSourceTestBase installs
// no writer, so the file on disk is the one the run's own $dumpports opened.
class ExtendedVcdStrengthFromSource : public VcdDumpFromSourceTestBase {
 protected:
  // Runs a module t holding `body` under a $dumpports that names its own file,
  // and returns what the run left in that file. The #1 puts a second time step
  // after the task: §21.7.3.1 starts the dumping "at the end of the current
  // simulation time unit", so the opening checkpoint the cases read is emitted
  // by the recording pass that follows time 0.
  std::string RunPortDump(const std::string& body) {
    RunSource("module t;\n" + body +
              "  initial begin\n"
              "    $dumpports(, \"strengths.vcd\");\n"
              "    #1;\n"
              "  end\n"
              "endmodule\n");
    return DumpFile("strengths.vcd");
  }

  // §21.7.4.2: a node information line is
  // "$var port <size> <<identifier_code> <reference> $end". Returns the
  // <-prefixed integer the declaration of `name` carries, or an empty string
  // when the file declares no port of that name.
  static std::string PortIdentifierCode(const std::string& content,
                                        const std::string& name) {
    for (const auto& line : Lines(content)) {
      auto fields = Tokens(line);
      if (fields.size() != 6 || fields[0] != "$var" || fields[1] != "port") {
        continue;
      }
      if (fields[4] == name) return fields[3];
    }
    return "";
  }

  // §21.7.4.3 (Syntax 21-29): a value change is
  // "p<port_value><0_strength_component><1_strength_component>", one space,
  // then the identifier_code. Returns the last such record written against
  // `name`, as "<port_value>|<0_strength_component><1_strength_component>",
  // so a failure reports the state characters and the strength digits apart
  // and a wrong digit is readable without counting characters. A file
  // declaring no such port, or holding no change against its code, answers
  // with a marker naming which of the two is missing.
  static std::string PortRecord(const std::string& content,
                                const std::string& name) {
    std::string code = PortIdentifierCode(content, name);
    if (code.empty()) return "<no-$var-port-" + name + ">";
    std::string record = "<no-change-" + code + ">";
    for (const auto& line : Lines(content)) {
      auto fields = Tokens(line);
      if (fields.size() != 2 || fields[0][0] != 'p' || fields[1] != code) {
        continue;
      }
      std::string body = fields[0].substr(1);
      if (body.size() < 3) return "<malformed-" + fields[0] + ">";
      record =
          body.substr(0, body.size() - 2) + "|" + body.substr(body.size() - 2);
    }
    return record;
  }
};

// §21.7.4.3: the 1_strength_component reports the strength1 specification for
// the port, and 5 is the digit the clause gives pull. §28.12.2 lets a
// continuous assignment carry a drive_strength, so a net assigned 1 under
// (pull0, pull1) is driven on its 1 side at pull and on its 0 side not at all
// -- the digits 0 and 5. The case fails on a writer that reports a port at
// strong whenever its value is not z, which writes 1|66 and leaves a reader
// unable to tell this net from one a plain assign drives.
TEST_F(ExtendedVcdStrengthFromSource, PullDrivenNetReportsThePullDigit) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|05") << content;
}

// §21.7.4.3: the components report the strength specification "for the port",
// so two ports of one design driven at two strengths carry two different
// records. Both nets here are assigned 1, one at pull (digit 5) and one at
// weak (digit 3), which leaves the strength components as the only thing
// separating the two records. The case fails on a writer that reports every
// port at one strength, which makes the two records identical apart from their
// identifier codes. The case above alone cannot say whether a writer does
// that, because one port is one record.
TEST_F(ExtendedVcdStrengthFromSource,
       TwoNetsAtDifferentStrengthsGetDifferentRecords) {
  auto content = RunPortDump(
      "  wire pu;\n"
      "  wire we;\n"
      "  assign (pull0, pull1) pu = 1'b1;\n"
      "  assign (weak0, weak1) we = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "pu"), "1|05") << content;
  EXPECT_EQ(PortRecord(content, "we"), "1|03") << content;
  EXPECT_NE(PortRecord(content, "pu"), PortRecord(content, "we")) << content;
}

// §21.7.4.3 numbers supply 7, the one strength above strong, so a writer that
// clamped every port at the strong digit would satisfy every case that drives
// below it and fail only this one. §6.6.6 gives a supply1 net supply strength
// on the 1 it drives, and §28.15.3 makes it carry that value with no driver
// connected, so the declaration alone settles both components: highz on the 0
// side, supply on the 1 side. The case fails on a writer that reports a driven
// port at strong, which writes 1|66.
TEST_F(ExtendedVcdStrengthFromSource, SupplyNetReportsTheSupplyDigit) {
  auto content = RunPortDump("  supply1 vdd;\n");
  EXPECT_EQ(PortRecord(content, "vdd"), "1|07") << content;
}

// §21.7.4.3: what the components report of a net is what §28.12 resolved for
// it, not what any one of its drivers was declared with. The two drivers here
// disagree in value and in strength, and the pull 0 outranks the weak 1, so
// the net settles to 0 at pull -- the digits 5 and 0. Every reading of a
// single driver's declaration gives some other pair: the first driver's is
// 5 and 5, the second's is 3 and 3, and the strongest declared level on each
// side is 5 and 5. A writer reporting a driven port at strong writes 0|66,
// which is none of them either.
TEST_F(ExtendedVcdStrengthFromSource,
       ResolvedStrengthOfTwoDriversReachesTheRecord) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b0;\n"
      "  assign (weak0, weak1) w = 1'b1;\n");
  EXPECT_EQ(PortRecord(content, "w"), "0|50") << content;
}

// §21.7.4.3 gives each component one digit while §28.12.3 lets a resolved
// strength span a range of levels, so a range has to be reduced to one digit.
// §21.7.4.3.2's only rule reducing two strengths to one takes "the stronger of
// the two", which makes the stronger bound of the range what a component
// reports. Two equal weak drivers of opposite value resolve to x with both
// sides spanning weak down to highz, so both components report weak, the digit
// 3. Nothing else in this file reaches an ambiguous strength: every other case
// resolves to a single level, where the two bounds coincide and the reduction
// cannot be observed. The case fails on a writer that reports a driven port at
// strong, which writes x|66.
TEST_F(ExtendedVcdStrengthFromSource,
       AmbiguousResolvedStrengthReportsTheStrongerBound) {
  auto content = RunPortDump(
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n");
  EXPECT_EQ(PortRecord(content, "w"), "x|33") << content;
}

}  // namespace
}  // namespace delta
