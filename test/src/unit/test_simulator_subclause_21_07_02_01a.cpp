#include <gtest/gtest.h>

#include <cstdlib>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "model_vcd_token_grammar.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdFileSyntaxSim : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(
        src, {.scope = "t",
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

bool IsDeclKeyword(const std::string& t) {
  static const char* kws[] = {"$comment", "$date",      "$enddefinitions",
                              "$scope",   "$timescale", "$upscope",
                              "$var",     "$version"};
  for (const char* k : kws) {
    if (t == k) return true;
  }
  return false;
}

bool IsSimSectionKeyword(const std::string& t) {
  return t == "$dumpall" || t == "$dumpoff" || t == "$dumpon" ||
         t == "$dumpvars";
}

std::string ConsumeValueChange(const std::vector<std::string>& toks,
                               size_t& i) {
  bool handled = false;
  std::string err = ConsumeFourStateValueChange(toks, i, handled);
  if (!handled) return "token is not a simulation command: " + toks[i];
  return err;
}

std::string CheckScopeSection(const VcdDeclarationCommand& cmd) {
  if (cmd.body.size() != 2 || !IsScopeType(cmd.body[0])) {
    return std::string("$scope requires scope_type + scope_identifier");
  }
  return std::string();
}

std::string CheckVarSection(const VcdDeclarationCommand& cmd) {
  if (cmd.body.size() != 4) {
    return std::string("$var body is not 4 elements");
  }
  if (!IsFourStateVarType(cmd.body[0])) {
    return "unknown var_type: " + cmd.body[0];
  }
  if (!IsDecimal(cmd.body[1])) {
    return "$var size not decimal: " + cmd.body[1];
  }
  if (!IsPrintableAscii(cmd.body[2])) {
    return "bad identifier code: " + cmd.body[2];
  }
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

std::string ValidateVcd(const std::vector<std::string>& toks) {
  size_t i = 0;
  std::string err =
      ConsumeDeclarationCommands(toks, i, IsDeclKeyword, CheckDeclarationBody);
  if (!err.empty()) return err;
  return ConsumeSimulationCommands(toks, i, IsSimSectionKeyword,
                                   ConsumeValueChange);
}

std::vector<std::string> VarDeclFor(const std::string& content,
                                    std::string_view name) {
  for (const auto& line : AllLines(content)) {
    auto toks = Tokens(line);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) return toks;
  }
  return {};
}

TEST_F(VcdFileSyntaxSim, WholeFileConformsToDumpFileGrammar) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    r = 0.0;\n"
      "    $dumpvars;\n"
      "    #10 begin a = 1'b1; v = 4'b1010; r = 2.5; end\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 begin a = 1'bx; v = 4'bzx10; end\n"
      "    #10 $dumplimit(1);\n"
      "    #10 a = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(ValidateVcd(toks), "");
  EXPECT_EQ(CountToken(toks, "$var"), 3u);
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);
}

TEST_F(VcdFileSyntaxSim, NamedEventDeclaresEventVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    $dumpvars;\n"
      "    #5 -> ev;\n"
      "  end\n"
      "endmodule\n");
  auto ev = VarDeclFor(content, "ev");
  ASSERT_EQ(ev.size(), 6u) << content;
  EXPECT_EQ(ev[1], "event");
  EXPECT_EQ(ev[2], "0");
  EXPECT_EQ(VarDeclFor(content, "clk").size(), 6u) << content;
}

TEST_F(VcdFileSyntaxSim, RegVariableDeclaresRegVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  reg [7:0] r;\n"
      "  initial begin\n"
      "    r = 8'h00;\n"
      "    $dumpvars;\n"
      "    #5 r = 8'hA5;\n"
      "  end\n"
      "endmodule\n");
  auto r = VarDeclFor(content, "r");
  ASSERT_EQ(r.size(), 6u) << content;
  EXPECT_EQ(r[1], "reg");
  EXPECT_EQ(r[2], "8");
}

TEST_F(VcdFileSyntaxSim, IntegerVariableDeclaresIntegerVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    $dumpvars;\n"
      "    #5 i = 7;\n"
      "  end\n"
      "endmodule\n");
  auto i = VarDeclFor(content, "i");
  ASSERT_EQ(i.size(), 6u) << content;
  EXPECT_EQ(i[1], "integer");
  EXPECT_EQ(i[2], "32");
}

TEST_F(VcdFileSyntaxSim, TimeVariableDeclaresTimeVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  time tm;\n"
      "  initial begin\n"
      "    tm = 0;\n"
      "    $dumpvars;\n"
      "    #5 tm = 64'd9;\n"
      "  end\n"
      "endmodule\n");
  auto tm = VarDeclFor(content, "tm");
  ASSERT_EQ(tm.size(), 6u) << content;
  EXPECT_EQ(tm[1], "time");
  EXPECT_EQ(tm[2], "64");
}

TEST_F(VcdFileSyntaxSim, ANetDeclaredBesideThemKeepsTheWireVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  reg r;\n"
      "  integer i;\n"
      "  time tm;\n"
      "  wire w;\n"
      "  assign w = r;\n"
      "  initial begin\n"
      "    r = 1'b0;\n"
      "    i = 0;\n"
      "    tm = 0;\n"
      "    $dumpvars;\n"
      "    #5 r = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto w = VarDeclFor(content, "w");
  ASSERT_EQ(w.size(), 6u) << content;
  EXPECT_EQ(w[1], "wire");
  auto r = VarDeclFor(content, "r");
  auto i = VarDeclFor(content, "i");
  auto tm = VarDeclFor(content, "tm");
  ASSERT_EQ(r.size(), 6u) << content;
  ASSERT_EQ(i.size(), 6u) << content;
  ASSERT_EQ(tm.size(), 6u) << content;
  EXPECT_EQ(r[1], "reg");
  EXPECT_EQ(i[1], "integer");
  EXPECT_EQ(tm[1], "time");
}

TEST_F(VcdFileSyntaxSim, DeclarationCommandsPrecedeSimulationCommands) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "    #10 begin a = 1'b1; v = 4'b1010; end\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  size_t last_decl = 0;
  size_t first_sim = toks.size();
  size_t last_var = 0;
  size_t end_defs = toks.size();
  for (size_t i = 0; i < toks.size(); ++i) {
    if (IsDeclKeyword(toks[i]) && toks[i] != "$comment") last_decl = i;
    if (toks[i] == "$var") last_var = i;
    if (toks[i] == "$enddefinitions") end_defs = i;
    if (first_sim == toks.size() &&
        (IsSimSectionKeyword(toks[i]) || toks[i][0] == '#')) {
      first_sim = i;
    }
  }
  ASSERT_LT(first_sim, toks.size());
  EXPECT_LT(last_decl, first_sim);
  EXPECT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  EXPECT_LT(last_var, end_defs);
}

TEST_F(VcdFileSyntaxSim, HeaderThenDefinitionsThenValueChanges) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto date = content.find("$date");
  auto version = content.find("$version");
  auto timescale = content.find("$timescale");
  auto scope = content.find("$scope");
  auto var = content.find("$var");
  auto end_defs = content.find("$enddefinitions");
  auto first_time = content.find("\n#");
  ASSERT_NE(date, std::string::npos);
  ASSERT_NE(first_time, std::string::npos);
  EXPECT_LT(date, version);
  EXPECT_LT(version, timescale);
  EXPECT_LT(timescale, scope);
  EXPECT_LT(scope, var);
  EXPECT_LT(var, end_defs);
  EXPECT_LT(end_defs, first_time);
}

TEST_F(VcdFileSyntaxSim, ScalarChangesUseFourStateValueCharacters) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 a = 1'bx;\n"
      "    #10 a = 1'bz;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

TEST_F(VcdFileSyntaxSim, VectorChangesUseBFormBinaryNumbers) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "    #10 v = 4'b1010;\n"
      "    #10 v = 4'bzx10;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b1010 !"));
  EXPECT_TRUE(HasLine(lines, "bzx10 !"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

TEST_F(VcdFileSyntaxSim, RealChangesUseRFormPreservingFullPrecision) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 0.0;\n"
      "    $dumpvars;\n"
      "    #10 r = 1.0 / 3.0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var real 64 ! r $end"), std::string::npos);
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "r0 !"));
  ASSERT_TRUE(HasLine(lines, "r0.3333333333333333 !"));
  const char* const kDumped = "0.3333333333333333";
  char* end = nullptr;
  const double kBack = std::strtod(kDumped, &end);
  ASSERT_EQ(*end, '\0');
  EXPECT_EQ(kBack, 1.0 / 3.0);
  for (const auto& l : lines) {
    EXPECT_FALSE(l.rfind("b", 0) == 0 && l.find(" !") != std::string::npos)
        << "real dumped as binary: " << l;
  }
}

TEST_F(VcdFileSyntaxSim, SimulationTimesAreAbsoluteDecimals) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #100 a = 1'b1;\n"
      "    #150 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "#100"));
  EXPECT_TRUE(HasLine(lines, "#250"));
  EXPECT_FALSE(HasLine(lines, "#150"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

TEST_F(VcdFileSyntaxSim, OnlyChangedVariablesListedPerIncrement) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #20 b = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto lines = AllLines(content);
  size_t t10 = 0;
  size_t t30 = lines.size();
  for (size_t i = 0; i < lines.size(); ++i) {
    if (lines[i] == "#10") t10 = i;
    if (lines[i] == "#30") t30 = i;
  }
  ASSERT_GT(t10, 0u);
  ASSERT_LT(t30, lines.size());
  for (size_t i = t10 + 1; i < t30; ++i) {
    EXPECT_EQ(lines[i].find('"'), std::string::npos)
        << "unchanged variable listed at #10: " << lines[i];
  }
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_GT(t30, t10);
  EXPECT_TRUE(HasLine(lines, "1\""));
}

TEST_F(VcdFileSyntaxSim, IdentifierCodesArePrintableAndDistinct) {
  std::string src = "module t;\n";
  for (int i = 0; i < 40; ++i) {
    src +=
        "  logic s" + std::to_string(i / 10) + std::to_string(i % 10) + ";\n";
  }
  src += "  initial begin\n";
  for (int i = 0; i < 40; ++i) {
    src += "    s" + std::to_string(i / 10) + std::to_string(i % 10) +
           " = 1'b0;\n";
  }
  src +=
      "    $dumpvars;\n"
      "    #10 s00 = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  auto toks = Tokens(RunVcd(src));
  ASSERT_FALSE(toks.empty());
  auto codes = CollectVarCodes(toks);
  ASSERT_EQ(codes.size(), 40u);
  std::set<std::string> unique;
  for (const auto& code : codes) {
    for (unsigned char c : code) {
      EXPECT_GE(c, 33) << "code below '!'";
      EXPECT_LE(c, 126) << "code above '~'";
    }
    unique.insert(code);
  }
  EXPECT_EQ(unique.size(), codes.size());
}

TEST_F(VcdFileSyntaxSim, MemoriesAreNotDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    mem[0] = 8'hAA;\n"
      "    $dumpvars;\n"
      "    #10 begin v = 8'hA5; mem[1] = 8'h55; end\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$var"), 1u);
  EXPECT_NE(content.find("$var reg 8 ! v $end"), std::string::npos);
  for (const auto& tok : toks) {
    EXPECT_EQ(tok.find("mem"), std::string::npos)
        << "memory reached the dump: " << tok;
  }
  EXPECT_TRUE(HasLine(AllLines(content), "b10100101 !"));
  EXPECT_EQ(ValidateVcd(toks), "");
}

TEST_F(VcdFileSyntaxSim, DynamicAndAssociativeArraysNotDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [7:0] d[];\n"
      "  int aa [int];\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    d = new[2];\n"
      "    d[0] = 8'h11;\n"
      "    aa[5] = 32'h22;\n"
      "    $dumpvars;\n"
      "    #10 begin a = 1'b1; d[1] = 8'h33; aa[6] = 32'h44; end\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$var"), 1u);
  EXPECT_NE(content.find("$var reg 1 ! a $end"), std::string::npos);
  EXPECT_EQ(CountToken(toks, "d"), 0u);
  EXPECT_EQ(CountToken(toks, "aa"), 0u);
  for (const auto& tok : toks) {
    EXPECT_FALSE(tok.rfind("d[", 0) == 0 || tok.rfind("aa[", 0) == 0)
        << "memory element reached the dump: " << tok;
  }
  EXPECT_EQ(ValidateVcd(toks), "");
}

TEST_F(VcdFileSyntaxSim, MultidimensionalArraysNotDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic [3:0] m [0:1][0:2];\n"
      "  initial begin\n"
      "    v = 4'h0;\n"
      "    m[0][1] = 4'h3;\n"
      "    $dumpvars;\n"
      "    #10 begin v = 4'hA; m[1][2] = 4'h7; end\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$var"), 1u);
  EXPECT_NE(content.find("$var reg 4 ! v $end"), std::string::npos);
  EXPECT_EQ(CountToken(toks, "m"), 0u);
  for (const auto& tok : toks) {
    EXPECT_FALSE(tok.rfind("m[", 0) == 0)
        << "multidim element reached the dump: " << tok;
  }
  EXPECT_EQ(ValidateVcd(toks), "");
}

TEST_F(VcdFileSyntaxSim, DumpvarsSelectionFormYieldsConformingSection) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 1'b0;\n"
      "    $dumpvars(0, a);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(ValidateVcd(toks), "");
  size_t open = toks.size();
  for (size_t i = 0; i < toks.size(); ++i) {
    if (toks[i] == "$dumpvars") open = i;
  }
  ASSERT_LT(open, toks.size());
  std::vector<std::string> body;
  for (size_t i = open + 1; i < toks.size() && toks[i] != "$end"; ++i) {
    body.push_back(toks[i]);
  }
  ASSERT_EQ(body.size(), 1u);
  EXPECT_EQ(body[0], "0!");
}

TEST_F(VcdFileSyntaxSim, TimescaleSectionMatchesTimeNumberTimeUnit) {
  const char* combos[] = {"1s", "10ms", "100us", "1ns", "10ps", "100fs"};
  for (const char* ts : combos) {
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader(ts);
      vcd.EndDefinitions();
    }
    auto content = ReadVcd();
    EXPECT_NE(content.find(std::string("$timescale\n  ") + ts + "\n$end"),
              std::string::npos)
        << "missing timescale section for " << ts;
    EXPECT_EQ(ValidateVcd(Tokens(content)), "") << "for " << ts;
  }
}

TEST_F(VcdFileSyntaxSim, PartOfVectorCannotBeDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'b10100101;\n"
      "    $dumpvars(1, v[2]);\n"
      "    #10 v = 8'b10100110;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(content.find("$enddefinitions"), std::string::npos);
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b10100101 !"));
  EXPECT_FALSE(HasLine(lines, "0!"));
  EXPECT_FALSE(HasLine(lines, "1!"));
  EXPECT_FALSE(HasLine(lines, "b101 !"));
  EXPECT_FALSE(HasLine(lines, "b1 !"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

TEST_F(VcdFileSyntaxSim, RangeOfVectorCannotBeDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'b10100101;\n"
      "    $dumpvars(1, v[3:0]);\n"
      "    #10 v = 8'b10100110;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(content.find("$enddefinitions"), std::string::npos);
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "b10100101 !"));
  EXPECT_FALSE(HasLine(lines, "b101 !"));
  EXPECT_FALSE(HasLine(lines, "0!"));
  EXPECT_FALSE(HasLine(lines, "1!"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

TEST_F(VcdFileSyntaxSim, ExpressionsCannotBeDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [1:0] a;\n"
      "  logic [1:0] b;\n"
      "  initial begin\n"
      "    a = 2'b01;\n"
      "    b = 2'b10;\n"
      "    $dumpvars(1, a + b);\n"
      "    #10 a = 2'b11;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_EQ(CountToken(toks, "$var"), 2u);
  auto codes = CollectVarCodes(toks);
  std::set<std::string> declared(codes.begin(), codes.end());
  for (size_t i = 0; i + 1 < toks.size(); ++i) {
    if (toks[i][0] == 'b' && IsFourStateDigits(toks[i].substr(1))) {
      EXPECT_TRUE(declared.count(toks[i + 1]))
          << "undeclared code after " << toks[i];
    }
  }
  EXPECT_EQ(ValidateVcd(toks), "");
}

TEST_F(VcdFileSyntaxSim, FileDataAreCaseSensitive) {
  auto content = RunVcd(
      "module t;\n"
      "  logic AB;\n"
      "  logic ab;\n"
      "  initial begin\n"
      "    AB = 1'b1;\n"
      "    ab = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 begin AB = 1'b0; ab = 1'b1; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var reg 1 ! AB $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 1 \" ab $end"), std::string::npos);
  auto lines = AllLines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "0\""));
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1\""));
}

TEST_F(VcdFileSyntaxSim, IdentifierCodesStayPrintablePastNinetyFour) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    for (int i = 0; i < 94; ++i) {
      auto* var = arena_.Create<Variable>();
      var->value = MakeLogic4VecVal(arena_, 1, 0);
      vcd.RegisterSignal("s", 1, var);
    }
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("wrap", 1, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1 ! wrap $end"), std::string::npos);
}

}  // namespace
}  // namespace delta
