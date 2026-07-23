#include <algorithm>
#include <cstdio>
#include <cstring>
#include <iterator>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_logic4vec.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.2.1: the syntax of the 4-state VCD file (Syntax 21-20) plus the
// subclause's prose rules about the file's contents (header first, absolute
// times, real vs. binary value forms, %.16g reals, printable identifier
// codes, no memory/strength/partial-vector/expression dumps, case-sensitive
// data). Every rule governs the file the dumper writes, so each test drives
// real SystemVerilog source -- declaring the dumped objects and invoking the
// §21.7.1.2-§21.7.1.5 dump-control tasks -- through parse, elaboration,
// lowering, and the scheduler with the driver's per-timestep recording loop
// installed, then checks the file against the grammar.
class VcdFileSyntaxSim : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents, mirroring the driver's registration
  // sequence (header, module scope, one registration per model variable,
  // $enddefinitions).
  std::string RunVcd(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // The context registers the dumpable objects in name order (the
      // alphabetically first gets '!', the next '"', and so on), applying the
      // §21.7.2.1 dumpability rules under test.
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts once the source's $dumpvars executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

std::vector<std::string> Lines(const std::string& content) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : content) {
    if (c == '\n') {
      out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

bool HasLine(const std::vector<std::string>& lines, std::string_view target) {
  for (const auto& l : lines) {
    if (l == target) return true;
  }
  return false;
}

size_t CountToken(const std::vector<std::string>& toks,
                  std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
}

// ---- Token-level validator for Syntax 21-20 ----
//
// The productions of Syntax 21-20 are all white-space-insensitive (§21.7.2
// established the file is free format), so validating the token stream
// validates the file. Each helper checks one terminal class of the grammar.

// identifier_code / scope_identifier / comment_text and friends: one or more
// ASCII characters; identifier codes must furthermore be printable (! to ~,
// decimal 33 to 126 -- the prose charset rule).
bool IsPrintableAscii(const std::string& t) {
  if (t.empty()) return false;
  for (unsigned char c : t) {
    if (c < 33 || c > 126) return false;
  }
  return true;
}

bool IsDecimal(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (c < '0' || c > '9') return false;
  }
  return true;
}

bool IsValueChar(char c) { return std::strchr("01xXzZ", c) != nullptr; }

// binary_number digits of a b-form vector_value_change: 4-state digits.
bool IsFourStateDigits(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (!IsValueChar(c)) return false;
  }
  return true;
}

bool IsScopeType(const std::string& t) {
  static const char* kinds[] = {"begin", "fork", "function", "module", "task"};
  for (const char* k : kinds) {
    if (t == k) return true;
  }
  return false;
}

bool IsVarType(const std::string& t) {
  static const char* types[] = {
      "event",   "integer", "parameter", "real", "realtime", "reg",
      "supply0", "supply1", "time",      "tri",  "triand",   "trior",
      "trireg",  "tri0",    "tri1",      "wand", "wire",     "wor"};
  for (const char* k : types) {
    if (t == k) return true;
  }
  return false;
}

// $timescale body: time_number (1|10|100) immediately followed (or separated
// by white space) by time_unit (s|ms|us|ns|ps|fs).
bool IsTimescaleBody(const std::string& body) {
  static const char* nums[] = {"100", "10", "1"};  // longest match first
  static const char* units[] = {"ms", "us", "ns", "ps", "fs", "s"};
  for (const char* n : nums) {
    if (body.rfind(n, 0) != 0) continue;
    std::string rest = body.substr(std::strlen(n));
    for (const char* u : units) {
      if (rest == u) return true;
    }
  }
  return false;
}

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

// Consumes one value_change at toks[i]: a scalar_value_change is a single
// token (value character immediately followed by the identifier code); a
// vector_value_change is a base-letter token (b/B + binary digits, or r/R + a
// real number) followed by the identifier code token. Returns "" on success.
std::string ConsumeValueChange(const std::vector<std::string>& toks,
                               size_t& i) {
  const std::string& t = toks[i];
  if (IsValueChar(t[0])) {
    if (t.size() < 2 || !IsPrintableAscii(t.substr(1))) {
      return "malformed scalar_value_change: " + t;
    }
    ++i;
    return "";
  }
  if (t[0] == 'b' || t[0] == 'B') {
    if (t.size() < 2 || !IsFourStateDigits(t.substr(1))) {
      return "malformed b-form vector_value_change: " + t;
    }
    if (i + 1 >= toks.size() || !IsPrintableAscii(toks[i + 1])) {
      return "b-form value without identifier code: " + t;
    }
    i += 2;
    return "";
  }
  if (t[0] == 'r' || t[0] == 'R') {
    if (t.size() < 2) return "empty r-form real number";
    char* endp = nullptr;
    std::strtod(t.c_str() + 1, &endp);
    if (endp != t.c_str() + t.size()) {
      return "malformed r-form real number: " + t;
    }
    if (i + 1 >= toks.size() || !IsPrintableAscii(toks[i + 1])) {
      return "r-form value without identifier code: " + t;
    }
    i += 2;
    return "";
  }
  return "token is not a simulation command: " + t;
}

// Validates the whole token stream against Syntax 21-20:
// value_change_dump_definitions ::= {declaration_command}{simulation_command}.
// Returns "" when the file conforms, else a description of the first
// violation.
std::string ValidateVcd(const std::vector<std::string>& toks) {
  size_t i = 0;
  // Declaration commands: each is $keyword [body] $end with a per-keyword
  // body shape.
  while (i < toks.size() && IsDeclKeyword(toks[i])) {
    std::string kw = toks[i++];
    std::vector<std::string> body;
    while (i < toks.size() && toks[i] != "$end") body.push_back(toks[i++]);
    if (i >= toks.size()) return kw + " not terminated by $end";
    ++i;  // past $end
    for (const auto& b : body) {
      if (!IsPrintableAscii(b)) return kw + " body has non-ASCII token: " + b;
    }
    if (kw == "$scope") {
      if (body.size() != 2 || !IsScopeType(body[0])) {
        return "$scope requires scope_type + scope_identifier";
      }
    } else if (kw == "$timescale") {
      std::string joined;
      for (const auto& b : body) joined += b;
      if (!IsTimescaleBody(joined)) {
        return "$timescale body is not time_number time_unit: " + joined;
      }
    } else if (kw == "$var") {
      if (body.size() != 4) return "$var body is not 4 elements";
      if (!IsVarType(body[0])) return "unknown var_type: " + body[0];
      if (!IsDecimal(body[1])) return "$var size not decimal: " + body[1];
      if (!IsPrintableAscii(body[2])) return "bad identifier code: " + body[2];
      if (!IsPrintableAscii(body[3])) return "bad reference: " + body[3];
    } else if (kw == "$upscope" || kw == "$enddefinitions") {
      if (!body.empty()) return kw + " carries an unexpected body";
    }
  }
  // Simulation commands: checkpoint sections, comments, timestamps, and bare
  // value changes. Any other $-keyword here is a declaration command showing
  // up after the simulation commands began, which the top production forbids.
  while (i < toks.size()) {
    const std::string& t = toks[i];
    if (IsSimSectionKeyword(t)) {
      std::string kw = t;
      ++i;
      while (i < toks.size() && toks[i] != "$end") {
        std::string err = ConsumeValueChange(toks, i);
        if (!err.empty()) return kw + " section: " + err;
      }
      if (i >= toks.size()) return kw + " not terminated by $end";
      ++i;
    } else if (t == "$comment") {
      ++i;
      while (i < toks.size() && toks[i] != "$end") ++i;
      if (i >= toks.size()) return "$comment not terminated by $end";
      ++i;
    } else if (t[0] == '#') {
      if (t.size() < 2 || !IsDecimal(t.substr(1))) {
        return "simulation_time is not # decimal_number: " + t;
      }
      ++i;
    } else if (t[0] == '$') {
      return "declaration command after simulation commands: " + t;
    } else {
      std::string err = ConsumeValueChange(toks, i);
      if (!err.empty()) return err;
    }
  }
  return "";
}

// Identifier codes declared by the file's $var commands, in order.
std::vector<std::string> CollectVarCodes(const std::vector<std::string>& toks) {
  std::vector<std::string> codes;
  for (size_t i = 0; i + 4 < toks.size(); ++i) {
    if (toks[i] == "$var") codes.push_back(toks[i + 3]);
  }
  return codes;
}

// Syntax 21-20 (whole grammar): a run that exercises a scalar, a vector, and
// a real variable through every checkpoint task of §21.7.1.2-§21.7.1.4 plus a
// §21.7.1.5 size limit yields a file whose entire token stream conforms to
// the value_change_dump_definitions production -- every declaration command
// shape, every simulation command shape, and every value form. Because the
// validator admits only the grammar's 4-state forms, its success also shows
// no strength information entered the file (prose: strength is not dumped).
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
  EXPECT_EQ(CountToken(toks, "$var"), 3u);  // a, r, v
  EXPECT_EQ(CountToken(toks, "$dumpvars"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  EXPECT_EQ(CountToken(toks, "$comment"), 1u);  // the $dumplimit notice
}

// Top production: {declaration_command} precedes {simulation_command} -- the
// last declaration keyword in the token stream sits before the first
// checkpoint section or timestamp, and $enddefinitions appears exactly once,
// after every $var.
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

// Prose: the file starts with header information (date, simulator version,
// timescale), next come the scope and variable-type definitions, and the
// value changes follow after those.
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

// scalar_value_change ::= value identifier_code with value ::= 0|1|x|X|z|Z: a
// scalar driven through all four logic states from procedural assignments
// records each state as its value character joined to the code.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

// vector_value_change (b-form): a packed vector's changes are recorded as the
// base letter b, binary_number digits drawn from the 4-state set (including x
// and z digits), and the identifier code. Prose: value changes for all
// non-real variables are specified in binary format.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b1010 !"));
  EXPECT_TRUE(HasLine(lines, "bzx10 !"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

// vector_value_change (r-form) + prose: a real variable's value changes are
// specified by real numbers written with a %.16g format, so all 53 mantissa
// bits of the IEEE Std 754 double survive; an application reading the value
// back with a %g scanf() recovers the identical double. The $var declaration
// for the variable uses the real var_type keyword.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "r0 !"));
  ASSERT_TRUE(HasLine(lines, "r0.3333333333333333 !"));
  // Application-program round trip: scanf's %g family reads the dumped text
  // back to exactly the double the simulation held.
  double back = 0.0;
  ASSERT_EQ(std::sscanf("0.3333333333333333", "%lg", &back), 1);
  EXPECT_EQ(back, 1.0 / 3.0);
  // The real is never rendered in the binary b-form.
  for (const auto& l : lines) {
    EXPECT_FALSE(l.rfind("b", 0) == 0 && l.find(" !") != std::string::npos)
        << "real dumped as binary: " << l;
  }
}

// simulation_time ::= # decimal_number, and prose: the recorded time is the
// absolute simulation time of the changes that follow, not a delta from the
// previous timestamp.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "#100"));
  EXPECT_TRUE(HasLine(lines, "#250"));
  EXPECT_FALSE(HasLine(lines, "#150"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

// Prose: only the variables that change value during a time increment are
// listed at that increment. Of two dumped scalars, the one that held its
// value contributes no value change under the increment's timestamp.
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
  auto lines = Lines(content);
  // a -> '!', b -> '"'. Between #10 and #30 only a's change appears.
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
  // b's high value is recorded only under its own increment.
  EXPECT_GT(t30, t10);
  EXPECT_TRUE(HasLine(lines, "1\""));
}

// identifier_code ::= {ASCII character} + prose: the generated codes are
// composed of the printable characters ! through ~ (decimal 33 to 126). With
// well under 94 dumped objects every code is also distinct, so each code
// represents one variable.
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

// Prose: memories are not dumped. An unpacked array declared alongside a
// packed vector contributes neither a $var declaration nor any value change
// -- element writes included -- while the packed vector (the closest
// accepted input) is still declared and dumped in full.
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
  EXPECT_NE(content.find("$var wire 8 ! v $end"), std::string::npos);
  for (const auto& tok : toks) {
    EXPECT_EQ(tok.find("mem"), std::string::npos)
        << "memory reached the dump: " << tok;
  }
  // The vector's change at #10 is recorded; the memory-element write is not.
  EXPECT_TRUE(HasLine(Lines(content), "b10100101 !"));
  EXPECT_EQ(ValidateVcd(toks), "");
}

// Prose: memories are not dumped, in every memory shape the model can hold. A
// dynamic array and an associative array declared beside a scalar contribute
// no $var declaration and no value change -- element writes before and after
// the checkpoint included -- while the scalar is dumped normally.
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
  EXPECT_NE(content.find("$var wire 1 ! a $end"), std::string::npos);
  EXPECT_EQ(CountToken(toks, "d"), 0u);
  EXPECT_EQ(CountToken(toks, "aa"), 0u);
  for (const auto& tok : toks) {
    EXPECT_FALSE(tok.rfind("d[", 0) == 0 || tok.rfind("aa[", 0) == 0)
        << "memory element reached the dump: " << tok;
  }
  EXPECT_EQ(ValidateVcd(toks), "");
}

// Prose: memories are not dumped -- the multidimensional unpacked array form.
// A two-dimension array takes a different lowering path than a single-dim one
// (per-dimension extents, doubly indexed element shadows), yet neither its
// whole-array entry nor any m[i][j] leaf reaches the file, while the packed
// vector beside it is dumped normally.
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
  EXPECT_NE(content.find("$var wire 4 ! v $end"), std::string::npos);
  EXPECT_EQ(CountToken(toks, "m"), 0u);
  for (const auto& tok : toks) {
    EXPECT_FALSE(tok.rfind("m[", 0) == 0)
        << "multidim element reached the dump: " << tok;
  }
  EXPECT_EQ(ValidateVcd(toks), "");
}

// simulation_command ($dumpvars section) built from the §21.7.1.2 selection
// form: when the task names an individual variable, the checkpoint section it
// leaves in the file still follows the grammar and holds exactly the selected
// object's value change -- the unselected variable contributes nothing inside
// the $dumpvars ... $end span.
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
  // The section between $dumpvars and its $end holds exactly a's record.
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
  EXPECT_EQ(body[0], "0!");  // a -> '!'; b's '"' never appears in the section
}

// $timescale body ::= time_number time_unit with time_number drawn from
// {1, 10, 100} and time_unit from {s, ms, us, ns, ps, fs}: for each sampled
// combination the header renders a $timescale section whose body is exactly
// that pair, and the whole file still validates. The section's rendering is
// the writer's own and does not depend on how the model was produced, so this
// boundary sweep drives the writer directly.
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

// Prose: the format has no mechanism to dump part of a vector -- the entire
// vector is dumped. A $dumpvars argument that selects a bit of the vector
// (the closest rejected input) yields no narrower record: every change for
// the vector is the full-width b-form and no scalar-form change for its code
// ever appears.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b10100101 !"));
  // No single-bit record for the vector's identifier code.
  EXPECT_FALSE(HasLine(lines, "0!"));
  EXPECT_FALSE(HasLine(lines, "1!"));
  // No shortened form that would correspond to the 4-bit or 1-bit selection.
  EXPECT_FALSE(HasLine(lines, "b101 !"));
  EXPECT_FALSE(HasLine(lines, "b1 !"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

// Prose (second rejected shape): a range part-select of a vector -- the
// closest input to the subclause's own bits-8-to-15 illustration -- also
// cannot be dumped. Naming v[3:0] in $dumpvars produces no 4-bit record for
// the 8-bit vector's code: every recorded change stays full width.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b10100101 !"));
  // Neither the 4-bit selection (0101, shortened to b101) nor any scalar-form
  // record appears for the vector's code.
  EXPECT_FALSE(HasLine(lines, "b101 !"));
  EXPECT_FALSE(HasLine(lines, "0!"));
  EXPECT_FALSE(HasLine(lines, "1!"));
  EXPECT_EQ(ValidateVcd(Tokens(content)), "");
}

// Prose: expressions such as a + b cannot be dumped. Naming an expression in
// $dumpvars mints no new dumped object -- the file declares exactly the two
// operand variables and every value change carries one of their two codes,
// never a third code holding the sum.
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
  // Every b-form change is attributed to a declared code.
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

// Prose: data in the VCD file are case sensitive. Two variables whose names
// differ only in letter case are distinct dumped objects -- each keeps its
// declared spelling in its $var reference and its own identifier code, and
// their opposite values land on their respective codes.
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
  // Sorted registration: "AB" precedes "ab", so AB -> '!' and ab -> '"'.
  EXPECT_NE(content.find("$var wire 1 ! AB $end"), std::string::npos);
  EXPECT_NE(content.find("$var wire 1 \" ab $end"), std::string::npos);
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));   // AB's initial 1
  EXPECT_TRUE(HasLine(lines, "0\""));  // ab's initial 0
  EXPECT_TRUE(HasLine(lines, "0!"));   // AB's change
  EXPECT_TRUE(HasLine(lines, "1\""));  // ab's change
}

// identifier_code charset boundary: past '~' (decimal 126) the generated code
// wraps back to '!' rather than escaping the printable range -- the 95th
// registered object's code is again drawn from the ! to ~ set. The charset of
// a generated code does not depend on how the signal was produced, so this
// boundary is exercised against the writer directly.
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
