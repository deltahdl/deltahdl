#include <gtest/gtest.h>

#include <cstddef>
#include <fstream>
#include <string>
#include <vector>

#include "fixture_extended_vcd_from_source.h"
#include "fixture_vcd_dump_run.h"

namespace delta {
namespace {

class ExtendedVcdDriversSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }

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

  static std::string IdentOnPortLine(const std::vector<std::string>& tokens,
                                     const std::string& name) {
    if (tokens.size() < 2 || tokens[0] != "$var" || tokens[1] != "port") {
      return "";
    }
    for (size_t k = 2; k + 1 < tokens.size(); ++k) {
      if (tokens[k] == name && !tokens[k - 1].empty() &&
          tokens[k - 1][0] == '<') {
        return tokens[k - 1];
      }
    }
    return "";
  }

  static std::string IdentFor(const std::string& content,
                              const std::string& name) {
    for (auto& line : Lines(content)) {
      std::string ident = IdentOnPortLine(Tokens(line), name);
      if (!ident.empty()) return ident;
    }
    return "<none>";
  }

  std::string PortRecord(const std::string& content, const std::string& name) {
    std::string ident = IdentFor(content, name);
    if (ident == "<none>") return "<no-ident>";
    std::string found = "<no-change>";
    for (auto& line : Lines(content)) {
      if (line.empty() || line[0] != 'p') continue;
      auto t = Tokens(line);
      if (t.size() != 2 || t[1] != ident) continue;
      std::string body = t[0].substr(1);
      if (body.size() < 3) return "<malformed>";
      std::string value = body.substr(0, body.size() - 2);
      std::string strength = body.substr(body.size() - 2);
      found = value;
      found += '|';
      found += strength;
    }
    return found;
  }
};

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
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

TEST_F(ExtendedVcdDriversSim, ContinuousAssignmentDriverDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

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
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

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

TEST_F(ExtendedVcdDriversSim, UndrivenPortIsNotAnActiveDriver) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "F|00") << content;
}

struct ConflictCase {
  const char* direction;
  const char* inside;
  const char* outside;
  const char* record;
};

const ConflictCase kEveryConflict[] = {
    {"inout", "assign @ = 1'b0", "assign @ = 1'b0", "060"},
    {"inout", "assign (pull0, pull1) @ = 1'b0", "assign @ = 1'b0", "060"},
    {"inout", "assign @ = 1'b1", "assign (pull0, pull1) @ = 1'b1", "106"},
    {"inout", "assign (weak0, weak1) @ = 1'b0",
     "assign (weak0, weak1) @ = 1'b0", "030"},
    {"inout", "assign (weak0, weak1) @ = 1'b0", "assign @ = 1'b0", "d60"},
    {"inout", "assign (weak0, weak1) @ = 1'b0",
     "assign (pull0, pull1) @ = 1'b0", "d50"},
    {"inout", "assign (weak0, weak1) @ = 1'b1", "assign @ = 1'b1", "u06"},
    {"inout", "assign @ = 1'b0", "assign (weak0, weak1) @ = 1'b0", "l60"},
    {"inout", "assign (pull0, pull1) @ = 1'b0",
     "assign (weak0, weak1) @ = 1'b0", "l50"},
    {"inout", "assign (pull0, pull1) @ = 1'b1",
     "assign (weak0, weak1) @ = 1'b1", "h05"},
};

class ConflictsOfRealPorts : public ExtendedVcdFromSource {
 protected:
  void ExpectRecords(const std::vector<PortEnds>& ports,
                     const std::vector<std::string>& expected,
                     const std::string& child_items = "",
                     const std::string& top_items = "") {
    auto content = RunEnds(ports, child_items, top_items);
    for (size_t i = 0; i < ports.size(); ++i) {
      std::string port = "p" + std::to_string(i);
      EXPECT_EQ(Checkpoint(content, "$dumpports", "u", port), expected[i])
          << port << " inside '" << ports[i].inside << "' outside '"
          << ports[i].outside << "'\n"
          << content;
    }
  }
};

TEST_F(ConflictsOfRealPorts, EachRuleGivesItsValueAndStrength) {
  std::vector<PortEnds> ports;
  std::vector<std::string> expected;
  for (const auto& entry : kEveryConflict) {
    ports.push_back({entry.direction, entry.inside, entry.outside});
    expected.emplace_back(entry.record);
  }
  ExpectRecords(ports, expected);
}

TEST_F(ConflictsOfRealPorts, GatePrimitivesDriveEachEnd) {
  ExpectRecords({{"inout", "bufif1 (@, 1'b1, 1'b1)", "buf (@, 1'b0)"},
                 {"inout", "buf (weak0, weak1) (@, 1'b1)", "buf (@, 1'b1)"}},
                {"A66", "u06"});
}

TEST_F(ConflictsOfRealPorts, DISABLED_AUserDefinedPrimitiveDrivesTheOutputEnd) {
  RunSource(
      "primitive one_of(output o, input i);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module dut(inout p0);\n"
      "  one_of inner(p0, 1'b1);\n"
      "endmodule\n"
      "module t;\n"
      "  wire w0;\n"
      "  assign w0 = 1'b0;\n"
      "  dut u(w0);\n"
      "  initial $dumpports(u, \"udp.vcd\");\n"
      "endmodule\n");
  auto content = DumpFile("udp.vcd");
  EXPECT_EQ(
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "p0")),
      "A")
      << content;
}

TEST_F(ConflictsOfRealPorts, DISABLED_UserDefinedPrimitivesDriveEachEnd) {
  RunSource(
      "primitive one_of(output o, input i);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module dut(inout p0, inout p1);\n"
      "  one_of inner0(p0, 1'b1);\n"
      "  one_of inner1(p1, 1'b0);\n"
      "endmodule\n"
      "module t;\n"
      "  wire w0, w1;\n"
      "  one_of outer0(w0, 1'b0);\n"
      "  assign w1 = 1'b1;\n"
      "  dut u(w0, w1);\n"
      "  initial $dumpports(u, \"udp.vcd\");\n"
      "endmodule\n");
  auto content = DumpFile("udp.vcd");
  EXPECT_EQ(
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "p0")),
      "A")
      << content;
  EXPECT_EQ(
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "p1")),
      "B")
      << content;
}

TEST_F(ConflictsOfRealPorts, AProceduralAssignDrivesAnOutputPort) {
  RunSource(
      "module dut(output logic q);\n"
      "  initial begin\n"
      "    q = 1'b0;\n"
      "    #1 assign q = 1'b1;\n"
      "    #1 deassign q;\n"
      "    q = 1'b0;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  wire q;\n"
      "  dut u(q);\n"
      "  initial begin\n"
      "    $dumpports(u, \"pca.vcd\");\n"
      "    #3;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("pca.vcd");
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "q")), "LHL") << content;
}

TEST_F(ConflictsOfRealPorts, AForceInsideDrivesTheOutputEnd) {
  RunSource(
      "module dut(output o);\n"
      "  initial begin\n"
      "    #1 force o = 1'b1;\n"
      "    #1 release o;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  wire o;\n"
      "  dut u(o);\n"
      "  initial begin\n"
      "    $dumpports(u, \"force.vcd\");\n"
      "    #3;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("force.vcd");
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "o")).substr(0, 2), "TH")
      << content;
}

TEST_F(ConflictsOfRealPorts, DISABLED_ForcesAtEachEndOfAnInoutPort) {
  RunSource(
      "module dut(inout p0, inout p1);\n"
      "  assign p0 = 1'b0;\n"
      "  assign p1 = 1'b0;\n"
      "  initial #1 force p1 = 1'b1;\n"
      "endmodule\n"
      "module t;\n"
      "  wire w0, w1;\n"
      "  assign w0 = 1'b0;\n"
      "  assign w1 = 1'b0;\n"
      "  dut u(w0, w1);\n"
      "  initial begin\n"
      "    $dumpports(u, \"forces.vcd\");\n"
      "    #1 force w0 = 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("forces.vcd");
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "p0")), "0B") << content;
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "p1")), "0A") << content;
}

TEST_F(ConflictsOfRealPorts, DISABLED_AnInoutPortOnAPartSelect) {
  RunSource(
      "module dut(n[1:0]);\n"
      "  inout [3:0] n;\n"
      "  assign n[1:0] = 2'b10;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [1:0] w;\n"
      "  assign w = 2'b01;\n"
      "  dut u(w);\n"
      "  initial $dumpports(u, \"part.vcd\");\n"
      "endmodule\n");
  auto content = DumpFile("part.vcd");
  auto states =
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "n"));
  EXPECT_EQ(states.substr(states.size() < 2 ? 0 : states.size() - 2), "AB")
      << content;
}

TEST_F(ConflictsOfRealPorts, DISABLED_AnInoutPortOnABitSelect) {
  RunSource(
      "module dut(n[2]);\n"
      "  inout [3:0] n;\n"
      "  assign n[2] = 1'b1;\n"
      "endmodule\n"
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  dut u(w);\n"
      "  initial $dumpports(u, \"bit.vcd\");\n"
      "endmodule\n");
  auto content = DumpFile("bit.vcd");
  auto states =
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "n"));
  EXPECT_EQ(states.size() == 4 ? states.substr(1, 1) : states, "A") << content;
}

TEST_F(ConflictsOfRealPorts, DISABLED_AnInoutPortOnAConcatenation) {
  RunSource(
      "module dut({a, b});\n"
      "  inout a, b;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b0;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [1:0] w;\n"
      "  assign w = 2'b01;\n"
      "  dut u(w);\n"
      "  initial $dumpports(u, \"cat.vcd\");\n"
      "endmodule\n");
  auto content = DumpFile("cat.vcd");
  EXPECT_EQ(
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "a")),
      "A")
      << content;
  EXPECT_EQ(
      StatesFor(Section(content, "$dumpports"), PortCode(content, "u", "b")),
      "B")
      << content;
}

TEST_F(ConflictsOfRealPorts, AnInoutPortLinkedForInterconnectDelays) {
  {
    std::ofstream sdf(scratch_.dir / "link.sdf");
    sdf << "(DELAYFILE)\n";
  }
  ExpectRecords(
      {{"inout", "assign @ = 1'b1", "assign @ = 1'b0"},
       {"inout", "assign (weak0, weak1) @ = 1'b0", "assign @ = 1'b0"}},
      {"A66", "d60"}, "", "  initial $sdf_annotate(\"link.sdf\");\n");
}

}  // namespace
}  // namespace delta
