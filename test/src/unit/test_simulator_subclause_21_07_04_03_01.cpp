#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_extended_vcd_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"

namespace delta {
namespace {

class ExtendedVcdStateCharacterSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }

  static std::string PortStateChars(const std::string& content) {
    size_t nl_p = content.find("\np");
    if (nl_p == std::string::npos) return "<no-value-change>";
    size_t start = nl_p + 2;
    size_t space = content.find(' ', start);
    if (space == std::string::npos || space - start < 2) return "<malformed>";
    return content.substr(start, space - start - 2);
  }

  static std::string PortStateCharsFor(const std::string& content,
                                       const std::string& code) {
    for (const auto& line : AllLines(content)) {
      if (line.empty() || line[0] != 'p') continue;
      size_t space = line.find(' ');
      if (space == std::string::npos || space < 4) continue;
      if (line.substr(space) != " <" + code) continue;
      return line.substr(1, space - 3);
    }
    return "<no-such-record>";
  }
};

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

TEST_F(ExtendedVcdStateCharacterSim, EachVectorBitSelectsAStateCharacter) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic [3:0] bus;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    bus = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "1010") << content;
}

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

TEST_F(ExtendedVcdStateCharacterSim, HeaderOutputPortLowSelectsOutputLow) {
  auto content = RunPortVcd(
      "module t(output o);\n"
      "  assign o = 1'b0;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "L") << content;
}

TEST_F(ExtendedVcdStateCharacterSim, HeaderOutputPortHighSelectsOutputHigh) {
  auto content = RunPortVcd(
      "module t(output o);\n"
      "  assign o = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateChars(content), "H") << content;
}

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
  EXPECT_EQ(PortStateCharsFor(content, "0"), "1") << content;
}

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

TEST_F(ExtendedVcdStateCharacterSim, ConcatenatedPortMembersAreInputPorts) {
  auto content = RunPortVcd(
      "module addbit({A, b}, ci);\n"
      "  input A, b, ci;\n"
      "endmodule\n"
      "module t;\n"
      "  logic x, y, z;\n"
      "  addbit u({x, y}, z);\n"
      "  initial begin\n"
      "    x = 1'b1; y = 1'b0; z = 1'b1;\n"
      "    $dumpports;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var port 1 <0 A $end"), std::string::npos)
      << content;
  EXPECT_NE(content.find("$var port 1 <1 b $end"), std::string::npos)
      << content;
  EXPECT_EQ(PortStateCharsFor(content, "0"), "U") << content;
  EXPECT_EQ(PortStateCharsFor(content, "1"), "D") << content;
  EXPECT_EQ(PortStateCharsFor(content, "2"), "U") << content;
}

TEST_F(ExtendedVcdStateCharacterSim, OutputWithTwoActiveDriversIsLowercase) {
  auto content = RunPortVcd(
      "module s(output hi, output lo);\n"
      "  assign hi = 1'b1;\n"
      "  assign hi = 1'b1;\n"
      "  assign lo = 1'b0;\n"
      "  assign lo = 1'b0;\n"
      "endmodule\n"
      "module t;\n"
      "  wire wa, wb;\n"
      "  s k1(.hi(wa), .lo(wb));\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateCharsFor(content, "0"), "h") << content;
  EXPECT_EQ(PortStateCharsFor(content, "1"), "l") << content;
}

TEST_F(ExtendedVcdStateCharacterSim, InputWithTwoActiveDriversIsLowercase) {
  auto content = RunPortVcd(
      "module s(input hi, input lo);\n"
      "endmodule\n"
      "module t;\n"
      "  wire wa, wb;\n"
      "  assign wa = 1'b1;\n"
      "  assign wa = 1'b1;\n"
      "  assign wb = 1'b0;\n"
      "  assign wb = 1'b0;\n"
      "  s k1(.hi(wa), .lo(wb));\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortStateCharsFor(content, "0"), "u") << content;
  EXPECT_EQ(PortStateCharsFor(content, "1"), "d") << content;
}

TEST_F(ExtendedVcdStateCharacterSim, InoutEndsPickTheConflictCharacter) {
  auto content = RunPortVcd(
      "module m1(inout p); assign p = 1'b1; endmodule\n"
      "module m0(inout p); assign p = 1'b0; endmodule\n"
      "module mx(inout p); assign p = 1'bx; endmodule\n"
      "module mw(inout p); assign (weak0, weak1) p = 1'b1; endmodule\n"
      "module mv(inout p); assign (weak0, weak1) p = 1'b0; endmodule\n"
      "module mn(inout p); endmodule\n"
      "module mz(inout p); assign p = 1'bz; endmodule\n"
      "module t;\n"
      "  wire wa, wb, wc, wd, we, wf, wg, wh, wi, wj, wk, wl, wm, wn, wo, wp;\n"
      "  assign wa = 1'b0;\n"
      "  assign wb = 1'b1;\n"
      "  assign (weak0, weak1) wc = 1'b1;\n"
      "  assign wd = 1'b1;\n"
      "  assign we = 1'b1;\n"
      "  assign wf = 1'b0;\n"
      "  assign wf = 1'b1;\n"
      "  assign wg = 1'bx;\n"
      "  assign wh = 1'b0;\n"
      "  assign wi = 1'b1;\n"
      "  assign wj = 1'bx;\n"
      "  assign wl = 1'b0;\n"
      "  assign wm = 1'b0;\n"
      "  assign (weak0, weak1) wn = 1'b0;\n"
      "  assign wp = 1'bz;\n"
      "  m1 ka(.p(wa));\n"
      "  mw kb(.p(wb));\n"
      "  m1 kc(.p(wc));\n"
      "  m1 kd(.p(wd));\n"
      "  m0 ke(.p(we));\n"
      "  m0 kf(.p(wf));\n"
      "  m1 kg(.p(wg));\n"
      "  mx kh(.p(wh));\n"
      "  mx ki(.p(wi));\n"
      "  mx kj(.p(wj));\n"
      "  m1 kk(.p(wk));\n"
      "  m0 kl(.p(wl));\n"
      "  mv km(.p(wm));\n"
      "  m0 kn(.p(wn));\n"
      "  mn ko(.p(wo));\n"
      "  mz kp(.p(wp));\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  const char* expected[] = {"A", "u", "h", "1", "B", "C", "c", "a",
                            "b", "?", "1", "0", "d", "l", "F", "f"};
  for (int code = 0; code < 16; ++code) {
    EXPECT_EQ(PortStateCharsFor(content, std::to_string(code)), expected[code])
        << code << "\n"
        << content;
  }
}

struct StateCase {
  const char* direction;
  const char* inside;
  const char* outside;
  char state;
};

const StateCase kEveryStateCharacter[] = {
    {"input", "", "assign @ = 1'b0", 'D'},
    {"input", "", "assign @ = 1'b1", 'U'},
    {"input", "", "assign @ = 1'bx", 'N'},
    {"input", "", "assign @ = 1'bz", 'Z'},
    {"inout", "assign (weak0, weak1) @ = 1'b0", "assign @ = 1'b0", 'd'},
    {"inout", "assign (weak0, weak1) @ = 1'b1", "assign @ = 1'b1", 'u'},
    {"output", "assign @ = 1'b0", "", 'L'},
    {"output", "assign @ = 1'b1", "", 'H'},
    {"output", "assign @ = 1'bx", "", 'X'},
    {"output", "assign @ = 1'bz", "", 'T'},
    {"inout", "assign @ = 1'b0", "assign (weak0, weak1) @ = 1'b0", 'l'},
    {"inout", "assign @ = 1'b1", "assign (weak0, weak1) @ = 1'b1", 'h'},
    {"inout", "assign @ = 1'b0", "assign @ = 1'b0", '0'},
    {"inout", "assign @ = 1'b1", "assign @ = 1'b1", '1'},
    {"inout", "assign @ = 1'bx", "assign @ = 1'bx", '?'},
    {"inout", "", "", 'F'},
    {"inout", "assign @ = 1'b1", "assign @ = 1'b0", 'A'},
    {"inout", "assign @ = 1'bx", "assign @ = 1'b0", 'a'},
    {"inout", "assign @ = 1'b0", "assign @ = 1'b1", 'B'},
    {"inout", "assign @ = 1'bx", "assign @ = 1'b1", 'b'},
    {"inout", "assign @ = 1'b0", "assign @ = 1'bx", 'C'},
    {"inout", "assign @ = 1'b1", "assign @ = 1'bx", 'c'},
    {"inout", "assign @ = 1'bz", "assign @ = 1'bz", 'f'},
};

class StateCharactersOfRealPorts : public ExtendedVcdFromSource {};

TEST_F(StateCharactersOfRealPorts, EachStateComesFromThePortsTwoEnds) {
  std::vector<PortEnds> ports;
  for (const auto& entry : kEveryStateCharacter) {
    ports.push_back({entry.direction, entry.inside, entry.outside});
  }
  auto content = RunEnds(ports);
  for (size_t i = 0; i < ports.size(); ++i) {
    std::string port = "p" + std::to_string(i);
    auto record = Checkpoint(content, "$dumpports", "u", port);
    EXPECT_EQ(record.substr(0, 1),
              std::string(1, kEveryStateCharacter[i].state))
        << port << " " << ports[i].direction << " inside '" << ports[i].inside
        << "' outside '" << ports[i].outside << "'\n"
        << content;
  }
}

TEST_F(StateCharactersOfRealPorts,
       AnInputChangeIsWrittenWithTheInputCharacters) {
  RunSource(
      "module dut(input i);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  dut u(v);\n"
      "  initial begin\n"
      "    $dumpports(u, \"in.vcd\");\n"
      "    #1 v = 1'b1;\n"
      "    #1 v = 1'bx;\n"
      "    #1 v = 1'bz;\n"
      "    #1 v = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("in.vcd");
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "i")), "DUNZD")
      << content;
}

TEST_F(StateCharactersOfRealPorts,
       AnOutputChangeIsWrittenWithTheOutputCharacters) {
  RunSource(
      "module dut(output o);\n"
      "  logic v = 1'b0;\n"
      "  assign o = v;\n"
      "  initial begin\n"
      "    #1 v = 1'b1;\n"
      "    #1 v = 1'bx;\n"
      "    #1 v = 1'bz;\n"
      "    #1 v = 1'b0;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  wire o;\n"
      "  dut u(o);\n"
      "  initial begin\n"
      "    $dumpports(u, \"out.vcd\");\n"
      "    #6;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("out.vcd");
  EXPECT_EQ(StatesFor(content, PortCode(content, "u", "o")), "LHXTL")
      << content;
}

}  // namespace
}  // namespace delta
