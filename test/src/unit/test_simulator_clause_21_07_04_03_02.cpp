#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.3.2 (Drivers) is the semantic companion to the extended-VCD port
// value change. It is a description, not a grammar: it contains no BNF
// production and no "shall" sentence. Its declarative content is:
//
//   Claim 1 (driver definition). A port's dumped value is resolved only from
//     drivers that are primitives, continuous assignments, or procedural
//     continuous assignments. A port with none of these is not an active
//     driver.
//   Claim 2 (conflict states). The port_value characters 0 and 1 mean both an
//     input and an output are active with that same value; 0 and 1 are the
//     conflict states.
//   Claim 3 (conflict resolution). When an input driver and an output driver
//     disagree, the resolved character and strength depend on the two drive
//     strengths: equal strength range -> 0/1 with the stronger strength; strong
//     input over weak output -> d/u with the input strength; weak input under
//     strong output -> l/h with the output strength.
//   Claim 4 (strength range). Strengths 7..5 are "strong"; strengths 4..1 are
//     "weak" -- the partition Claim 3 compares.
//
// Only Claim 1 is reachable through this simulator. The port value change is
// emitted by VcdWriter::WritePortValueChange (src/simulator/vcd_writer.cpp),
// which reads a single resolved 4-state value per bit through LogicBitToChar
// (only 0/1/x/z) and writes a fixed strength pair -- strong (6) for a driven
// bit, highz (0) for a high-impedance bit. The Variable/VcdSignal model keeps
// no record of drive direction, of separate input versus output contributions,
// or of a per-driver strength. So Claims 2-4, which all require decomposing a
// port into an input driver and an output driver and comparing their strength
// ranges, cannot be exercised: the conflict characters d/u/l/h (and the
// direction-tagged 0/1 conflict semantics) are unreachable here, exactly as the
// dependency subclause §21.7.4.3.1 established for the character vocabulary.
//
// These tests observe Claim 1 through the production path. Each of the three
// driver kinds §21.7.4.3.2 admits is built from real source syntax, elaborated,
// lowered, and run under $dumpports; the writer then dumps the port it drives
// as an active (strong-strength) port, and an undriven port -- the negative of
// Claim 1 -- as high-impedance at highz strength. The dependency subclauses
// §21.7.4.3 (the p<value><s0><s1> form and its strength components) and
// §21.7.4.2 (the $var port declaration that names the identifier code) supply
// the record the driver's resolved value flows into.
class ExtendedVcdDriversSim : public VcdTestBase {
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

  // Split a whitespace-separated line into tokens.
  static std::vector<std::string> Tokens(const std::string& line) {
    std::vector<std::string> out;
    size_t i = 0;
    while (i < line.size()) {
      while (i < line.size() && (line[i] == ' ' || line[i] == '\t')) ++i;
      size_t start = i;
      while (i < line.size() && line[i] != ' ' && line[i] != '\t') ++i;
      if (i > start) out.push_back(line.substr(start, i - start));
    }
    return out;
  }

  // Read a line by index within the file content.
  static std::vector<std::string> Lines(const std::string& content) {
    std::vector<std::string> out;
    size_t pos = 0;
    while (pos <= content.size()) {
      size_t nl = content.find('\n', pos);
      if (nl == std::string::npos) {
        if (pos < content.size()) out.push_back(content.substr(pos));
        break;
      }
      out.push_back(content.substr(pos, nl - pos));
      pos = nl + 1;
    }
    return out;
  }

  // §21.7.4.2: each $var port line records the identifier code (a <-prefixed
  // integer) and the port name. Return the identifier token (e.g. "<0") that
  // was assigned to the named port.
  static std::string IdentFor(const std::string& content,
                              const std::string& name) {
    for (auto& line : Lines(content)) {
      auto t = Tokens(line);
      if (t.size() >= 2 && t[0] == "$var" && t[1] == "port") {
        // Layout: $var port <size|[range]> <code> <name> $end
        for (size_t k = 2; k + 1 < t.size(); ++k) {
          if (t[k] == name && k >= 1 && !t[k - 1].empty() &&
              t[k - 1][0] == '<') {
            return t[k - 1];
          }
        }
      }
    }
    return "<none>";
  }

  // Extended-VCD value change for a named port: the p-record whose trailing
  // identifier token matches the port's $var code. Returns
  // "<port_value>|<s0s1>"
  // -- the state character run and the two strength component digits -- or a
  // diagnostic marker.
  std::string PortRecord(const std::string& content, const std::string& name) {
    std::string ident = IdentFor(content, name);
    if (ident == "<none>") return "<no-ident>";
    std::string found = "<no-change>";
    for (auto& line : Lines(content)) {
      if (line.empty() || line[0] != 'p') continue;
      auto t = Tokens(line);
      if (t.size() != 2 || t[1] != ident) continue;
      // t[0] == "p<value><s0><s1>"
      std::string body = t[0].substr(1);
      if (body.size() < 3) return "<malformed>";
      std::string value = body.substr(0, body.size() - 2);
      std::string strength = body.substr(body.size() - 2);
      found = value + "|" + strength;
    }
    return found;
  }
};

// §21.7.4.3.2 Claim 1: a gate primitive is a driver. Instantiating buf so it
// drives the net w, then dumping w under $dumpports, resolves w's value from
// that primitive. The writer reports w as an active port: the state character
// is the driven value (1) and the strength pair is the driven (strong) 66,
// never the highz 00 an undriven port would carry.
TEST_F(ExtendedVcdDriversSim, PrimitiveDriverDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a;\n"
      "  wire w;\n"
      "  buf (w, a);\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|66") << content;
}

// §21.7.4.3.2 Claim 1: a continuous assignment is a driver. A net resolved by
// assign is dumped as an active port -- driven value, strong strength.
TEST_F(ExtendedVcdDriversSim, ContinuousAssignmentDriverDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|66") << content;
}

// §21.7.4.3.2 Claim 1: a procedural continuous assignment is a driver. This
// driver kind has two syntactic forms; the force/release form is one. Forcing a
// net high with a force statement drives it, and the writer dumps it as an
// active port -- driven value, strong strength -- just like the other two
// driver kinds.
TEST_F(ExtendedVcdDriversSim,
       ForceProceduralContinuousAssignmentDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|66") << content;
}

// §21.7.4.3.2 Claim 1: the assign/deassign form is the other syntactic position
// of the procedural continuous assignment driver kind, and it takes a different
// production path than force. A variable driven by a procedural assign is
// dumped as an active port -- driven value, strong strength -- confirming this
// form counts as a driver too.
TEST_F(ExtendedVcdDriversSim,
       AssignProceduralContinuousAssignmentDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    assign v = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "v"), "1|66") << content;
}

// §21.7.4.3.2 Claim 1, negative form: a port with none of the three driver
// kinds is not an active driver. An undriven net resolves to high impedance, so
// the writer dumps it with the high-impedance state character z and the highz
// strength pair 00 -- distinct from the strong 66 an active driver produces.
// This is the closest input Claim 1 must reject as "driven".
TEST_F(ExtendedVcdDriversSim, UndrivenPortIsNotAnActiveDriver) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "z|00") << content;
}

}  // namespace
}  // namespace delta
