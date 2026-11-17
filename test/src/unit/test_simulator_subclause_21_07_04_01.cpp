#include <gtest/gtest.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_extended_vcd_from_source.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_logic4vec.h"
#include "model_vcd_token_grammar.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class ExtendedVcdSyntaxSim : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src, bool close_file = false) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .close_file = close_file});
  }
};

bool IsPortValueChars(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (std::strchr("DUNZduLHXTlh01?FAaBbCcfxz", c) == nullptr) return false;
  }
  return true;
}

bool IsStrengthDigit(char c) { return c >= '0' && c <= '7'; }

bool IsPortSize(const std::string& t) {
  if (t == "1") return true;
  if (t.size() < 5 || t.front() != '[' || t.back() != ']') return false;
  size_t colon = t.find(':');
  if (colon == std::string::npos) return false;
  return IsDecimal(t.substr(1, colon - 1)) &&
         IsDecimal(t.substr(colon + 1, t.size() - colon - 2));
}

bool IsPortIdentifierCode(const std::string& t) {
  return t.size() >= 2 && t[0] == '<' && IsDecimal(t.substr(1));
}

bool IsDeclKeyword(const std::string& t) {
  static const char* kws[] = {"$comment", "$date",      "$enddefinitions",
                              "$scope",   "$timescale", "$upscope",
                              "$var",     "$vcdclose",  "$version"};
  for (const char* k : kws) {
    if (t == k) return true;
  }
  return false;
}

bool IsSimSectionKeyword(const std::string& t) {
  return t == "$dumpports" || t == "$dumpportsoff" || t == "$dumpportson" ||
         t == "$dumpportsall" || t == "$dumpvars" || t == "$dumpall" ||
         t == "$dumpoff" || t == "$dumpon";
}

std::string ConsumeValueChange(const std::vector<std::string>& toks,
                               size_t& i) {
  bool handled = false;
  std::string err = ConsumeFourStateValueChange(toks, i, handled);
  if (handled) return err;

  const std::string& t = toks[i];
  if (t[0] == 'p') {
    if (t.size() < 4 || !IsStrengthDigit(t[t.size() - 2]) ||
        !IsStrengthDigit(t[t.size() - 1]) ||
        !IsPortValueChars(t.substr(1, t.size() - 3))) {
      return "malformed p-form value: " + t;
    }
    if (i + 1 >= toks.size() || !IsPortIdentifierCode(toks[i + 1])) {
      return "p-form value without < identifier code: " + t;
    }
    i += 2;
    return "";
  }
  return "token is not a simulation command: " + t;
}

bool OpensHeaderDeclaration(const std::string& t) {
  return IsDeclKeyword(t) && t != "$vcdclose";
}

std::string CheckScopeSection(const VcdDeclarationCommand& cmd) {
  if (cmd.body.size() != 2 || cmd.body[0] != "module") {
    return std::string(
        "$scope requires the module scope_type + scope_identifier");
  }
  return std::string();
}

std::string CheckPortVarSizeAndCode(const VcdDeclarationCommand& cmd) {
  if (!IsPortSize(cmd.body[1])) {
    return "$var port size: " + cmd.body[1];
  }
  if (!IsPortIdentifierCode(cmd.body[2])) {
    return "$var port identifier code: " + cmd.body[2];
  }
  return std::string();
}

std::string CheckVarTypeAndSize(const VcdDeclarationCommand& cmd) {
  if (cmd.body[0] == "port") return CheckPortVarSizeAndCode(cmd);
  if (!IsFourStateVarType(cmd.body[0])) {
    return "unknown var_type: " + cmd.body[0];
  }
  if (!IsDecimal(cmd.body[1])) {
    return "$var size not decimal: " + cmd.body[1];
  }
  return std::string();
}

std::string CheckVarSection(const VcdDeclarationCommand& cmd) {
  if (cmd.body.size() != 4) {
    return std::string("$var body is not 4 elements");
  }
  std::string err = CheckVarTypeAndSize(cmd);
  if (!err.empty()) return err;
  if (!IsPrintableAscii(cmd.body[3])) {
    return "bad reference: " + cmd.body[3];
  }
  return std::string();
}

std::string CheckDeclarationBody(const VcdDeclarationCommand& cmd) {
  if (cmd.keyword == "$scope") return CheckScopeSection(cmd);
  if (cmd.keyword == "$var") return CheckVarSection(cmd);
  return std::string();
}

std::string ConsumeVcdCloseCommand(const std::vector<std::string>& toks,
                                   size_t& i, bool& handled) {
  if (toks[i] != "$vcdclose") return std::string();
  handled = true;
  if (i + 2 >= toks.size() || toks[i + 1][0] != '#' ||
      !IsDecimal(toks[i + 1].substr(1)) || toks[i + 2] != "$end") {
    return std::string(
        "$vcdclose is not followed by final_simulation_time $end");
  }
  i += 3;
  return std::string();
}

std::string ValidateEvcd(const std::vector<std::string>& toks) {
  size_t i = 0;
  std::string err = ConsumeDeclarationCommands(toks, i, OpensHeaderDeclaration,
                                               CheckDeclarationBody);
  if (!err.empty()) return err;
  return ConsumeSimulationCommands(toks, i, IsSimSectionKeyword,
                                   ConsumeValueChange, ConsumeVcdCloseCommand);
}

TEST_F(ExtendedVcdSyntaxSim, WholeFileConformsToExtendedDumpFileGrammar) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic [7:0] v = 8'h81;\n"
      "  real r = 0.5;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 begin a = 1'b1; v = 8'h93; end\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "    #10 a = 1'bx;\n"
      "    #10 a = 1'bz;\n"
      "  end\n"
      "endmodule\n",
      true);
  auto toks = Tokens(content);
  ASSERT_EQ(CountToken(toks, "$var"), 3u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  EXPECT_EQ(ValidateEvcd(toks), "");
}

TEST_F(ExtendedVcdSyntaxSim, DeclarationCommandsPrecedeSimulationCommands) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic [3:0] v = 4'b1010;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  size_t end_defs = IndexOf(toks, "$enddefinitions");
  for (size_t i = end_defs; i < toks.size(); ++i) {
    EXPECT_NE(toks[i], "$var") << "$var after $enddefinitions";
    EXPECT_NE(toks[i], "$scope") << "$scope after $enddefinitions";
  }
  for (size_t i = 0; i < end_defs; ++i) {
    EXPECT_NE(toks[i][0], '#') << "simulation time among declarations";
  }
}

TEST_F(ExtendedVcdSyntaxSim, HeaderThenPortDefinitionsThenValueChanges) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  size_t date = IndexOf(toks, "$date");
  size_t version = IndexOf(toks, "$version");
  size_t timescale = IndexOf(toks, "$timescale");
  size_t scope = IndexOf(toks, "$scope");
  size_t var = IndexOf(toks, "$var");
  size_t end_defs = IndexOf(toks, "$enddefinitions");
  size_t first_time = IndexOf(toks, "#0");
  ASSERT_LT(first_time, toks.size());
  EXPECT_LT(date, version);
  EXPECT_LT(version, timescale);
  EXPECT_LT(timescale, scope);
  EXPECT_LT(scope, var);
  EXPECT_LT(var, end_defs);
  EXPECT_LT(end_defs, first_time);
}

TEST_F(ExtendedVcdSyntaxSim, OnlyChangedPortsListedPerTimeIncrement) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] moved = 8'h81;\n"
      "  logic [7:0] still = 8'hA5;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 moved = 8'h83;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10000001 !"), std::string::npos);
  EXPECT_NE(content.find("b10100101 \""), std::string::npos);
  size_t t10 = content.find("\n#10");
  ASSERT_NE(t10, std::string::npos);
  EXPECT_NE(content.find("b10000011 !", t10), std::string::npos);
  EXPECT_EQ(content.find("b10100101", t10), std::string::npos);
}

TEST_F(ExtendedVcdSyntaxSim, SimulationTimesRecordAbsoluteTime) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #15 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "#25"));
  EXPECT_FALSE(HasLine(lines, "#15"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

TEST_F(ExtendedVcdSyntaxSim, ScalarChangesUseBinaryStateCharacters) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 a = 1'bx;\n"
      "    #10 a = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

TEST_F(ExtendedVcdSyntaxSim, VectorChangesUseBinaryStateCharactersWithXAndZ) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v = 8'h00;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b10xz01zx !"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

TEST_F(ExtendedVcdSyntaxSim, RealValuesUseFullPrecisionScanfReadableForm) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 0.0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 1.0 / 3.0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  ASSERT_TRUE(HasLine(lines, "r0.3333333333333333 !"));
  EXPECT_EQ(content.find("r0.333333 "), std::string::npos);
  const char* const kDumped = "0.3333333333333333";
  char* field_end = nullptr;
  const double kBack = std::strtod(kDumped, &field_end);
  ASSERT_EQ(*field_end, '\0');
  EXPECT_EQ(kBack, 1.0 / 3.0);
}

TEST_F(ExtendedVcdSyntaxSim, RealFromDeclarationInitializerUsesFullPrecision) {
  auto content = RunVcd(
      "module t;\n"
      "  real r = 1.0 / 7.0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 2.0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  char expected[64];
  std::snprintf(expected, sizeof(expected), "r%.16g !", 1.0 / 7.0);
  ASSERT_TRUE(HasLine(lines, expected));
  EXPECT_EQ(content.find("r0.142857 "), std::string::npos);
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

TEST_F(ExtendedVcdSyntaxSim, WholeVectorDumpedNeverAPartSelect) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [15:0] v = 16'h8001;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 16'h8003;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b1000000000000001 !"), std::string::npos);
  EXPECT_NE(content.find("b1000000000000011 !"), std::string::npos);
  EXPECT_EQ(content.find('['), std::string::npos);
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

TEST_F(ExtendedVcdSyntaxSim, DataAreCaseSensitive) {
  auto content = RunVcd(
      "module t;\n"
      "  logic sigA = 1'b1;\n"
      "  logic siga = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 siga = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var reg 1 ! sigA $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 1 \" siga $end"), std::string::npos);
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "0\""));
  EXPECT_TRUE(HasLine(lines, "1\""));
}

TEST_F(ExtendedVcdSyntaxSim, MatchingFourStateConstructNamesAreEquivalent) {
  const char* body =
      "  logic a = 1'b0;\n"
      "  logic [3:0] v = 4'b1010;\n"
      "  initial begin\n"
      "%s"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  auto src = [&](const char* dump_call) {
    char buf[512];
    std::snprintf(buf, sizeof(buf), body, dump_call);
    return std::string("module t;\n") + buf;
  };
  auto four_state =
      RunVcd(src("    $dumpfile(\"dump1.dump\");\n"
                 "    $dumpvars;\n"));
  auto extended = RunVcd(src("    $dumpports(, \"dump2.dump\");\n"));
  auto tokse = Tokens(extended);
  ASSERT_EQ(CountToken(tokse, "$var"), 2u);
  auto shared_lines = [](const std::string& content) {
    std::vector<std::string> out;
    for (const auto& l : AllLines(content)) {
      if (l.rfind("$var ", 0) == 0 || l.rfind("$scope ", 0) == 0 ||
          l == "$upscope $end" || l == "$enddefinitions $end") {
        out.push_back(l);
      }
    }
    return out;
  };
  EXPECT_EQ(shared_lines(extended), shared_lines(four_state));
  for (const auto& t : tokse) {
    EXPECT_NE(t[0], '*') << "star-prefixed construct name: " << t;
  }
  for (const auto& t : Tokens(four_state)) {
    EXPECT_NE(t[0], '*') << "star-prefixed construct name: " << t;
  }
}

TEST_F(ExtendedVcdSyntaxSim, CloseCommandCarriesFinalSimulationTime) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      true);
  auto toks = Tokens(content);
  size_t close = IndexOf(toks, "$vcdclose");
  ASSERT_LT(close + 2, toks.size());
  EXPECT_EQ(toks[close + 1][0], '#');
  EXPECT_TRUE(IsDecimal(toks[close + 1].substr(1)));
  EXPECT_EQ(toks[close + 2], "$end");
  EXPECT_EQ(close + 3, toks.size());
  EXPECT_EQ(ValidateEvcd(toks), "");
}

TEST_F(ExtendedVcdSyntaxSim, ValidatorRejectsNonConformantStreams) {
  using V = std::vector<std::string>;
  EXPECT_EQ(ValidateEvcd(V{"$enddefinitions", "$end", "#10", "1!"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions$end", "#10", "1!"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "#10ns", "1!"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "#10", "*1!"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "$dumpportsx", "$end"}),
            "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "p0", "<0"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "p066", "!"}), "");
}

TEST_F(ExtendedVcdSyntaxSim, PortFormCheckpointUsesDumpportsKeyword) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("t");
    auto* scalar = arena_.Create<Variable>();
    scalar->value = MakeScalar(arena_, 0, 0);
    vcd.RegisterSignal("p0", 1, scalar);
    auto* bus = arena_.Create<Variable>();
    bus->value = MakeLogic4VecVal(arena_, 4, 0xA);
    vcd.RegisterSignal(VcdSignalSpec{"data", 4, bus, NetType::kWire, 3, 0});
    vcd.EndScope();
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpports"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 0u);
  EXPECT_NE(content.find("$var port 1 <0 p0 $end"), std::string::npos);
  EXPECT_NE(content.find("$var port [3:0] <1 data $end"), std::string::npos);
  EXPECT_NE(content.find("p066 <0"), std::string::npos);
  EXPECT_NE(content.find("p101066 <1"), std::string::npos);
  EXPECT_EQ(ValidateEvcd(toks), "");
}

TEST_F(ExtendedVcdSyntaxSim, PortFormControlSectionsUseDumpportsKeywords) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* port = arena_.Create<Variable>();
    port->value = MakeScalar(arena_, 1, 0);
    vcd.RegisterSignal("p0", 1, port);
    vcd.EndDefinitions();
    vcd.DumpAll(10);
    vcd.DumpOff(20);
    vcd.DumpOn(30);
  }
  auto toks = Tokens(ReadVcd());
  EXPECT_EQ(CountToken(toks, "$dumpportsall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpportsoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpportson"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 0u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 0u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 0u);
}

TEST_F(ExtendedVcdSyntaxSim, PortValuesCarryBinaryStateAndStrength) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.SetExtendedPortNodes();
    vcd.WriteHeader("1ns");
    auto* p0 = arena_.Create<Variable>();
    p0->value = MakeScalar(arena_, 0, 0);
    vcd.RegisterSignal("p0", 1, p0);
    auto* p1 = arena_.Create<Variable>();
    p1->value = MakeScalar(arena_, 1, 0);
    vcd.RegisterSignal("p1", 1, p1);
    auto* px = arena_.Create<Variable>();
    px->value = MakeScalar(arena_, 1, 1);
    vcd.RegisterSignal("px", 1, px);
    auto* pz = arena_.Create<Variable>();
    pz->value = MakeScalar(arena_, 0, 1);
    vcd.RegisterSignal("pz", 1, pz);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto toks = Tokens(ReadVcd());
  EXPECT_EQ(CountToken(toks, "p066"), 1u);
  EXPECT_EQ(CountToken(toks, "p166"), 1u);
  EXPECT_EQ(CountToken(toks, "p?66"), 1u);
  EXPECT_EQ(CountToken(toks, "pF00"), 1u);
  for (const char* v : {"p066", "p166", "p?66", "pF00"}) {
    std::string t = v;
    EXPECT_TRUE(IsStrengthDigit(t[t.size() - 2]));
    EXPECT_TRUE(IsStrengthDigit(t[t.size() - 1]));
  }
}

std::string VersionSectionOf(const std::string& content) {
  auto start = content.find("$version");
  if (start == std::string::npos) return {};
  auto end = content.find("$end", start);
  if (end == std::string::npos) return content.substr(start);
  return content.substr(start, end - start);
}

class ExtendedVcdVersionCommands : public VcdDumpFromSourceTestBase {
 protected:
  static std::string DesignCalling(const std::string& tasks) {
    return "module n;\n"
           "  logic [7:0] p;\n"
           "  initial p = 8'h11;\n"
           "endmodule\n"
           "module t;\n"
           "  n k1();\n"
           "  n k2();\n"
           "  logic [7:0] q;\n"
           "  initial begin\n"
           "    q = 8'h00;\n" +
           tasks +
           "    #1 q = 8'h22;\n"
           "  end\n"
           "endmodule\n";
  }
};

TEST_F(ExtendedVcdVersionCommands, VersionTextNamesTheDumpportsCall) {
  RunSource(DesignCalling("    $dumpports(k1, \"ports.vcd\");\n"));
  auto version = VersionSectionOf(DumpFile("ports.vcd"));
  ASSERT_FALSE(version.empty()) << DumpFile("ports.vcd");
  EXPECT_TRUE(Holds(version, "$dumpports(k1,\"ports.vcd\")")) << version;
}

TEST_F(ExtendedVcdVersionCommands, VersionTextListsEveryDumpportsCall) {
  RunSource(
      DesignCalling("    $dumpports(k1);\n"
                    "    $dumpports(k2);\n"));
  auto version = VersionSectionOf(DumpFile("dumpports.vcd"));
  ASSERT_FALSE(version.empty()) << DumpFile("dumpports.vcd");
  EXPECT_TRUE(Holds(version, "$dumpports(k1)")) << version;
  EXPECT_TRUE(Holds(version, "$dumpports(k2)")) << version;
}

TEST_F(ExtendedVcdVersionCommands, FourStateVersionTextCarriesNoDumpportsCall) {
  RunSource(
      DesignCalling("    $dumpfile(\"vars.vcd\");\n"
                    "    $dumpvars;\n"
                    "    $dumpports(k1);\n"));
  auto version = VersionSectionOf(DumpFile("vars.vcd"));
  ASSERT_FALSE(version.empty()) << DumpFile("vars.vcd");
  EXPECT_FALSE(Holds(version, "$dumpports")) << version;
}

bool IsExtendedDeclarationKeyword(const std::string& t) {
  return t == "$comment" || t == "$date" || t == "$enddefinitions" ||
         t == "$scope" || t == "$timescale" || t == "$upscope" || t == "$var" ||
         t == "$version";
}

bool IsExtendedSimulationKeyword(const std::string& t) {
  return t == "$dumpports" || t == "$dumpportsoff" || t == "$dumpportson" ||
         t == "$dumpportsall";
}

std::string DeclarationBodyViolation(const std::vector<std::string>& toks,
                                     size_t i, size_t end) {
  if (toks[i] == "$var" &&
      (end - i != 5 || toks[i + 1] != "port" || !IsPortSize(toks[i + 2]) ||
       !IsPortIdentifierCode(toks[i + 3]))) {
    return "not a port $var: " + toks[i + 1];
  }
  if (toks[i] == "$scope" && (end - i != 3 || toks[i + 1] != "module")) {
    return "not a module $scope: " + toks[i + 1];
  }
  return "";
}

std::string StrictDeclarationViolation(const std::vector<std::string>& toks,
                                       size_t& i) {
  while (i < toks.size() && toks[i] != "$enddefinitions") {
    const std::string& keyword = toks[i];
    if (!IsExtendedDeclarationKeyword(keyword)) {
      return "not a declaration keyword: " + keyword;
    }
    size_t end = i + 1;
    while (end < toks.size() && toks[end] != "$end") ++end;
    if (end == toks.size()) return "unterminated " + keyword;
    std::string err = DeclarationBodyViolation(toks, i, end);
    if (!err.empty()) return err;
    i = end + 1;
  }
  if (i + 1 >= toks.size() || toks[i + 1] != "$end") {
    return "no $enddefinitions $end";
  }
  i += 2;
  return "";
}

std::string StrictValueChangeViolation(const std::vector<std::string>& toks,
                                       size_t& i) {
  const std::string& t = toks[i];
  if (t.size() < 4 || t[0] != 'p' || t.size() != 4 ||
      !IsPortValueChars(t.substr(1, 1)) || !IsStrengthDigit(t[2]) ||
      !IsStrengthDigit(t[3])) {
    return "not a port value change: " + t;
  }
  if (i + 1 >= toks.size() || !IsPortIdentifierCode(toks[i + 1])) {
    return "no port identifier code after " + t;
  }
  i += 2;
  return "";
}

std::string StrictSimulationViolation(const std::vector<std::string>& toks,
                                      size_t& i) {
  while (i < toks.size()) {
    const std::string& t = toks[i];
    if ((t[0] == '#' && IsDecimal(t.substr(1))) ||
        IsExtendedSimulationKeyword(t) || t == "$end") {
      ++i;
    } else if (t == "$vcdclose") {
      if (i + 2 >= toks.size() || toks[i + 1][0] != '#' ||
          toks[i + 2] != "$end") {
        return "malformed $vcdclose";
      }
      i += 3;
    } else {
      std::string err = StrictValueChangeViolation(toks, i);
      if (!err.empty()) return err;
    }
  }
  return "";
}

std::string StrictExtendedViolation(const std::string& content) {
  auto toks = Tokens(content);
  size_t i = 0;
  std::string err = StrictDeclarationViolation(toks, i);
  if (!err.empty()) return err;
  return StrictSimulationViolation(toks, i);
}

class ExtendedFileFromARun : public ExtendedVcdFromSource {
 protected:
  std::string RunScalarPorts() {
    RunSource(
        "module dut(input a, output b);\n"
        "  assign b = a;\n"
        "endmodule\n"
        "module t;\n"
        "  logic a = 1'b0;\n"
        "  wire b;\n"
        "  dut u(a, b);\n"
        "  initial begin\n"
        "    $dumpports(u, \"run.vcd\");\n"
        "    #10 a = 1'b1;\n"
        "    #10 $dumpportsall;\n"
        "    #10 $dumpportsoff;\n"
        "    #10 $dumpportson;\n"
        "    #10 a = 1'bx;\n"
        "    #10 a = 1'bz;\n"
        "  end\n"
        "endmodule\n");
    return DumpFile("run.vcd");
  }
};

TEST_F(ExtendedFileFromARun, DISABLED_TheWholeFileFollowsTheExtendedSyntax) {
  auto content = RunScalarPorts();
  EXPECT_EQ(StrictExtendedViolation(content), "") << content;
}

TEST_F(ExtendedFileFromARun, SectionsAreKeyedByTheDumpportsFamily) {
  auto content = RunScalarPorts();
  auto toks = Tokens(content);
  EXPECT_EQ(CountToken(toks, "$dumpports"), 1u) << content;
  EXPECT_EQ(CountToken(toks, "$dumpportsall"), 1u) << content;
  EXPECT_EQ(CountToken(toks, "$dumpportsoff"), 1u) << content;
  EXPECT_EQ(CountToken(toks, "$dumpportson"), 1u) << content;
  for (const char* keyword : {"$dumpvars", "$dumpall", "$dumpoff", "$dumpon"}) {
    EXPECT_EQ(CountToken(toks, keyword), 0u) << keyword << "\n" << content;
  }
}

TEST_F(ExtendedFileFromARun, SharedConstructsAreWrittenAsInTheFourStateFile) {
  RunSource(
      "module dut(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  wire b;\n"
      "  dut u(a, b);\n"
      "  initial begin\n"
      "    $dumpfile(\"four.vcd\");\n"
      "    $dumpvars(0, u);\n"
      "    $dumpports(u, \"run.vcd\");\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n");
  auto extended = DumpFile("run.vcd");
  auto four = DumpFile("four.vcd");
  EXPECT_EQ(Section(extended, "$timescale"), Section(four, "$timescale"))
      << extended << four;
  for (const auto& tok : Tokens(extended)) {
    EXPECT_NE(tok[0], '*') << tok << "\n" << extended;
  }
  for (const char* keyword :
       {"$date", "$version", "$timescale", "$enddefinitions"}) {
    EXPECT_EQ(CountToken(Tokens(extended), keyword), 1u) << keyword << "\n"
                                                         << extended;
    EXPECT_EQ(CountToken(Tokens(four), keyword), 1u) << keyword << "\n" << four;
  }
}

TEST_F(ExtendedFileFromARun, DISABLED_ARealPortIsWrittenAtSixteenDigits) {
  RunSource(
      "module dut(input real rp);\n"
      "endmodule\n"
      "module t;\n"
      "  real r = 0.0;\n"
      "  dut u(r);\n"
      "  initial begin\n"
      "    $dumpports(u, \"real.vcd\");\n"
      "    #1 r = 1.0 / 3.0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("real.vcd");
  auto code = PortCode(content, "u", "rp");
  EXPECT_NE(content.find("0.3333333333333333 " + code + "\n"),
            std::string::npos)
      << content;
}

TEST_F(ExtendedFileFromARun, AVectorPortIsWrittenWhole) {
  RunSource(
      "module dut(input [3:0] n);\n"
      "endmodule\n"
      "module t;\n"
      "  logic [3:0] v = 4'b0000;\n"
      "  dut u(v[3:0]);\n"
      "  initial begin\n"
      "    $dumpports(u, \"vector.vcd\");\n"
      "    #1 v = 4'b1010;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n");
  auto content = DumpFile("vector.vcd");
  auto code = PortCode(content, "u", "n");
  EXPECT_EQ(StatesFor(content, code), "DDDDUDUD") << content;
  EXPECT_NE(content.find(" [3:0] " + code + " n "), std::string::npos)
      << content;
}

}  // namespace
}  // namespace delta
