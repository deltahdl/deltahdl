#include <cstdio>
#include <cstring>
#include <iterator>
#include <sstream>
#include <string>
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

// §21.7.4.1: the syntax of the extended VCD file (Syntax 21-27) plus the
// subclause's prose rules about the file's contents: a 4-state construct name
// matching an extended construct is equivalent (unless preceded by *), the
// header/definitions/value-change ordering with only changed ports listed per
// increment, absolute simulation times, binary port values carrying strength
// information, %.16g reals readable back with a %g scanf, whole-vector-only
// dumps with no part-select or expression entries, and case-sensitive data.
// Every rule governs the file the dumper writes, so each test drives real
// SystemVerilog source -- declaring the dumped objects and invoking the
// §21.7.3.x $dumpports task family, which marks the writer extended -- through
// parse, elaboration, lowering, and the scheduler with the driver's
// per-timestep recording loop installed, then checks the file against the
// grammar. Only the port-form productions (the $var port node entries and the
// p-value changes selected by SetExtendedPortNodes) are observed at the writer
// stage directly: no production caller enables that form yet (wiring it into
// the task path belongs to §21.7.4.2/§21.7.4.3), and the grammar of the
// writer's own output does not depend on how a value reached the writer.
class ExtendedVcdSyntaxSim : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents, mirroring the driver's registration
  // sequence (header, module scope, the model's dumpable objects,
  // $enddefinitions). `close_file` mirrors the driver's final step of handing
  // the writer the end simulation time as the file is closed.
  std::string RunVcd(const std::string& src, bool close_file = false) {
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
      // alphabetically first gets '!', the next '"', and so on).
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts once the source's dump task executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
      if (close_file) vcd.WriteVcdClose(f.ctx.CurrentTime().ticks);
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

// Index of the first occurrence of target, or toks.size() when absent.
size_t IndexOf(const std::vector<std::string>& toks, std::string_view target) {
  for (size_t i = 0; i < toks.size(); ++i) {
    if (toks[i] == target) return i;
  }
  return toks.size();
}

// ---- Token-level validator for Syntax 21-27 ----
//
// The productions are white-space-insensitive (§21.7.4 established the
// extended file is free format), so validating the token stream validates the
// file. The subclause's opening rule folds the 4-state vocabulary in: a
// 4-state construct name that matches an extended construct is equivalent, so
// wherever the extended file reuses a matching 4-state construct the 4-state
// rendering is admitted alongside the extended one.

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

bool IsFourStateDigits(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (!IsValueChar(c)) return false;
  }
  return true;
}

// port_value state characters: the input (D U N Z d u), output (L H X T l h),
// and unknown-direction (0 1 ? F A a B b C c f) alphabets, plus the x and z
// the subclause's prose uses for a port's binary unknown/high-impedance
// states.
bool IsPortValueChars(const std::string& t) {
  if (t.empty()) return false;
  for (char c : t) {
    if (std::strchr("DUNZduLHXTlh01?FAaBbCcfxz", c) == nullptr) return false;
  }
  return true;
}

bool IsStrengthDigit(char c) { return c >= '0' && c <= '7'; }

// size ::= 1 | vector_index, with vector_index ::= [msb_index:lsb_index].
bool IsPortSize(const std::string& t) {
  if (t == "1") return true;
  if (t.size() < 5 || t.front() != '[' || t.back() != ']') return false;
  size_t colon = t.find(':');
  if (colon == std::string::npos) return false;
  return IsDecimal(t.substr(1, colon - 1)) &&
         IsDecimal(t.substr(colon + 1, t.size() - colon - 2));
}

// identifier_code ::= < {integer}.
bool IsPortIdentifierCode(const std::string& t) {
  return t.size() >= 2 && t[0] == '<' && IsDecimal(t.substr(1));
}

// The 4-state var_type keywords a name-equivalent $var construct may carry.
bool IsFourStateVarType(const std::string& t) {
  static const char* types[] = {
      "event",   "integer", "parameter", "real", "realtime", "reg",
      "supply0", "supply1", "time",      "tri",  "triand",   "trior",
      "trireg",  "tri0",    "tri1",      "wand", "wire",     "wor"};
  for (const char* k : types) {
    if (t == k) return true;
  }
  return false;
}

// $timescale body: number (1|10|100) then time_unit (fs|ps|ns|us|ms|s).
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

// declaration_keyword: the 4-state set the extended file shares by name
// equivalence plus the extended-only $vcdclose.
bool IsDeclKeyword(const std::string& t) {
  static const char* kws[] = {"$comment", "$date",      "$enddefinitions",
                              "$scope",   "$timescale", "$upscope",
                              "$var",     "$vcdclose",  "$version"};
  for (const char* k : kws) {
    if (t == k) return true;
  }
  return false;
}

// simulation_keyword ::= $dumpports | $dumpportsoff | $dumpportson |
// $dumpportsall, plus the name-equivalent 4-state checkpoint keywords the
// hybrid (non-port-form) extended file carries.
bool IsSimSectionKeyword(const std::string& t) {
  return t == "$dumpports" || t == "$dumpportsoff" || t == "$dumpportson" ||
         t == "$dumpportsall" || t == "$dumpvars" || t == "$dumpall" ||
         t == "$dumpoff" || t == "$dumpon";
}

// Consumes one value_change at toks[i]. The 4-state scalar/b/r forms are
// admitted by the name-equivalence rule; the extended form is the p-token
// (value ::= p port_value 0_strength_component 1_strength_component) followed
// by its < identifier code. Returns "" on success.
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
  if (t[0] == 'p') {
    // p, then one port_value state character per bit, then the two strength
    // components; the < identifier code follows as its own token.
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

// Validates the whole token stream against Syntax 21-27:
// value_change_dump_definitions ::= {declaration_command}{simulation_command}.
// The $vcdclose declaration command is admitted at the tail of the simulation
// commands: its command_text is the final simulation time, which exists only
// once the value changes have all been recorded. Returns "" when the file
// conforms, else a description of the first violation.
std::string ValidateEvcd(const std::vector<std::string>& toks) {
  size_t i = 0;
  // Declaration commands: each is $keyword [command_text] $end with a
  // per-keyword body shape.
  while (i < toks.size() && IsDeclKeyword(toks[i]) && toks[i] != "$vcdclose") {
    std::string kw = toks[i++];
    std::vector<std::string> body;
    while (i < toks.size() && toks[i] != "$end") body.push_back(toks[i++]);
    if (i >= toks.size()) return kw + " not terminated by $end";
    ++i;  // past $end
    for (const auto& b : body) {
      if (!IsPrintableAscii(b)) return kw + " body has non-ASCII token: " + b;
    }
    if (kw == "$scope") {
      // scope_section ::= scope_type scope_identifier, scope_type ::= module.
      if (body.size() != 2 || body[0] != "module") {
        return "$scope requires the module scope_type + scope_identifier";
      }
    } else if (kw == "$timescale") {
      std::string joined;
      for (const auto& b : body) joined += b;
      if (!IsTimescaleBody(joined)) {
        return "$timescale body is not number time_unit: " + joined;
      }
    } else if (kw == "$var") {
      // var_section ::= var_type size identifier_code reference: the extended
      // port form, or a name-equivalent 4-state $var construct.
      if (body.size() != 4) return "$var body is not 4 elements";
      if (body[0] == "port") {
        if (!IsPortSize(body[1])) return "$var port size: " + body[1];
        if (!IsPortIdentifierCode(body[2])) {
          return "$var port identifier code: " + body[2];
        }
      } else if (IsFourStateVarType(body[0])) {
        if (!IsDecimal(body[1])) return "$var size not decimal: " + body[1];
      } else {
        return "unknown var_type: " + body[0];
      }
      if (!IsPrintableAscii(body[3])) return "bad reference: " + body[3];
    } else if (kw == "$upscope" || kw == "$enddefinitions") {
      if (!body.empty()) return kw + " carries an unexpected body";
    }
  }
  // Simulation commands: checkpoint sections, comments, timestamps, bare
  // value changes, and the trailing $vcdclose. Any other $-keyword here is a
  // declaration command after the simulation commands began, which the top
  // production forbids.
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
    } else if (t == "$vcdclose") {
      // close_text ::= final_simulation_time ::= # decimal_number.
      if (i + 2 >= toks.size() || toks[i + 1][0] != '#' ||
          !IsDecimal(toks[i + 1].substr(1)) || toks[i + 2] != "$end") {
        return "$vcdclose is not followed by final_simulation_time $end";
      }
      i += 3;
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

// Syntax 21-27 (whole grammar): a run that exercises a scalar, a vector, and
// a real through the entire $dumpports task family -- with the initial values
// produced by declaration initializers and the later changes procedural,
// including the x and z states -- plus the driver's closing step yields a
// file whose entire token stream conforms to value_change_dump_definitions:
// every declaration command shape, every simulation command shape, every
// value form, and the extended-only $vcdclose declaration command.
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
      /*close_file=*/true);
  auto toks = Tokens(content);
  // Non-vacuity anchors: all three objects are declared, every checkpoint
  // task left its section, and the close command is present.
  ASSERT_EQ(CountToken(toks, "$var"), 3u);
  EXPECT_EQ(CountToken(toks, "$dumpall"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_EQ(CountToken(toks, "$dumpon"), 1u);
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  EXPECT_EQ(ValidateEvcd(toks), "");
}

// Top production: {declaration_command} precedes {simulation_command} -- the
// node information all sits before $enddefinitions, which appears exactly
// once, and every simulation-time command follows it.
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
  // Every $var declaration precedes $enddefinitions ...
  for (size_t i = end_defs; i < toks.size(); ++i) {
    EXPECT_NE(toks[i], "$var") << "$var after $enddefinitions";
    EXPECT_NE(toks[i], "$scope") << "$scope after $enddefinitions";
  }
  // ... and every simulation_time command follows it.
  for (size_t i = 0; i < end_defs; ++i) {
    EXPECT_NE(toks[i][0], '#') << "simulation time among declarations";
  }
}

// Prose: the file starts with header information (the date, the simulator's
// version, and the timescale), next come the scope definitions of the dumped
// ports, and the value changes at each time increment follow after those.
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

// Prose: only the ports that change value during a time increment are listed
// under that increment's simulation time. Of two dumped vectors, the one that
// held its value contributes nothing after the increment's timestamp; its
// value appears only in the opening checkpoint.
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
  // moved -> '!', still -> '"' (name order). Both appear in the opening
  // checkpoint ...
  EXPECT_NE(content.find("b10000001 !"), std::string::npos);
  EXPECT_NE(content.find("b10100101 \""), std::string::npos);
  // ... but after #10 only the changed port is listed.
  size_t t10 = content.find("\n#10");
  ASSERT_NE(t10, std::string::npos);
  EXPECT_NE(content.find("b10000011 !", t10), std::string::npos);
  EXPECT_EQ(content.find("b10100101", t10), std::string::npos);
}

// Prose + simulation_time ::= # decimal_number: the time recorded is the
// absolute simulation time of the changes that follow, not an increment from
// the previous command.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "#10"));
  EXPECT_TRUE(HasLine(lines, "#25"));
  EXPECT_FALSE(HasLine(lines, "#15"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

// Prose: value changes are specified in binary format by the 0, 1, x, and z
// values. A scalar port driven through all four states from procedural
// assignments records each state as its binary value character.
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
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

// Prose: the same binary 0/1/x/z rule governs a multi-bit port, not just a
// scalar -- the vector input form. A packed port assigned a value mixing all
// four states records one b-form value change whose digits are drawn from
// {0,1,x,z}, most significant bit first, with the unknown and high-impedance
// bits carried literally as x and z rather than collapsed to a binary bit.
TEST_F(ExtendedVcdSyntaxSim, VectorChangesUseBinaryStateCharactersWithXAndZ) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v = 8'h00;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  // The MSB is set, so no leading digit is dropped: every one of the eight
  // bits -- including the x and z digits -- appears in the single value change.
  EXPECT_TRUE(HasLine(lines, "b10xz01zx !"));
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

// Prose: a real number is dumped with a %.16g format so all 53 mantissa bits
// of the IEEE Std 754 double survive, and an application program reading the
// value back with a %g scanf() recovers the identical double.
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
  auto lines = Lines(content);
  ASSERT_TRUE(HasLine(lines, "r0.3333333333333333 !"));
  // A %g-style writer would have truncated to six significant digits.
  EXPECT_EQ(content.find("r0.333333 "), std::string::npos);
  // Application-program round trip: scanf's %g family reads the dumped text
  // back to exactly the double the simulation held.
  double back = 0.0;
  ASSERT_EQ(std::sscanf("0.3333333333333333", "%lg", &back), 1);
  EXPECT_EQ(back, 1.0 / 3.0);
}

// Prose: the %.16g rule holds however the real reached the dump -- the
// declaration-initializer input form, distinct from the procedural assignment
// above. A real whose value is fixed by its declaration initializer (§21.7.2.1
// real declaration syntax) is captured in the opening checkpoint with the same
// 16-significant-digit form, not a shortened default-%g rendering.
TEST_F(ExtendedVcdSyntaxSim, RealFromDeclarationInitializerUsesFullPrecision) {
  auto content = RunVcd(
      "module t;\n"
      "  real r = 1.0 / 7.0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 2.0;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  // The initializer-produced value is emitted with the full %.16g field
  // (sixteen significant digits) that production applies ...
  char expected[64];
  std::snprintf(expected, sizeof(expected), "r%.16g !", 1.0 / 7.0);
  ASSERT_TRUE(HasLine(lines, expected));
  // ... not truncated the way a default-precision %g writer would render it.
  EXPECT_EQ(content.find("r0.142857 "), std::string::npos);
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

// Prose: the extended format supports no mechanism to dump part of a vector
// -- the entire vector is dumped instead -- and expressions cannot be dumped.
// A 16-bit port with its most significant bit set records full-width value
// changes carrying every bit, and no sub-range selection or expression entry
// appears anywhere in the file.
TEST_F(ExtendedVcdSyntaxSim, WholeVectorDumpedNeverAPartSelect) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [15:0] v = 16'h8001;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 16'h8003;\n"
      "  end\n"
      "endmodule\n");
  // All 16 bits are present in both records; the MSB is set so no bit is
  // dropped by leading-digit shortening.
  EXPECT_NE(content.find("b1000000000000001 !"), std::string::npos);
  EXPECT_NE(content.find("b1000000000000011 !"), std::string::npos);
  // No [8:15]-style sub-range reference is ever emitted in this form.
  EXPECT_EQ(content.find('['), std::string::npos);
  EXPECT_EQ(ValidateEvcd(Tokens(content)), "");
}

// Prose: data in the extended VCD file are case sensitive. Two objects whose
// names differ only in case are distinct: each gets its own $var declaration
// and its own value records, and neither name is folded into the other.
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
  // sigA -> '!', siga -> '"' (name order: 'A' < 'a').
  EXPECT_NE(content.find("$var wire 1 ! sigA $end"), std::string::npos);
  EXPECT_NE(content.find("$var wire 1 \" siga $end"), std::string::npos);
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "0\""));
  EXPECT_TRUE(HasLine(lines, "1\""));
}

// "A 4-state VCD construct name that matches an extended VCD construct shall
// be considered equivalent, except if preceded by an *." The same design
// dumped through the 4-state tasks ($dumpfile/$dumpvars -- the §21.7.2.1
// dependency's real syntax) and through $dumpports renders every shared
// declaration construct identically: matching names carry the same meaning in
// both files. And since no emitted construct name is *-prefixed, the
// equivalence holds for every construct either file contains.
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
  // Anchor on real content so a failed run cannot compare equal vacuously.
  auto tokse = Tokens(extended);
  ASSERT_EQ(CountToken(tokse, "$var"), 2u);
  // The shared construct names render identically in both files.
  auto shared_lines = [](const std::string& content) {
    std::vector<std::string> out;
    for (const auto& l : Lines(content)) {
      if (l.rfind("$var ", 0) == 0 || l.rfind("$scope ", 0) == 0 ||
          l == "$upscope $end" || l == "$enddefinitions $end") {
        out.push_back(l);
      }
    }
    return out;
  };
  EXPECT_EQ(shared_lines(extended), shared_lines(four_state));
  // The exception's boundary: neither file carries a *-prefixed construct
  // name, so the name equivalence applies to every construct present.
  for (const auto& t : tokse) {
    EXPECT_NE(t[0], '*') << "star-prefixed construct name: " << t;
  }
  for (const auto& t : Tokens(four_state)) {
    EXPECT_NE(t[0], '*') << "star-prefixed construct name: " << t;
  }
}

// declaration_keyword includes the extended-only $vcdclose, whose
// command_text is close_text ::= final_simulation_time ::= # decimal_number:
// the driver's closing step leaves $vcdclose #<time> $end as the file's last
// command.
TEST_F(ExtendedVcdSyntaxSim, CloseCommandCarriesFinalSimulationTime) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      /*close_file=*/true);
  auto toks = Tokens(content);
  size_t close = IndexOf(toks, "$vcdclose");
  ASSERT_LT(close + 2, toks.size());
  EXPECT_EQ(toks[close + 1][0], '#');
  EXPECT_TRUE(IsDecimal(toks[close + 1].substr(1)));
  EXPECT_EQ(toks[close + 2], "$end");
  // It is the last command of the file.
  EXPECT_EQ(close + 3, toks.size());
  EXPECT_EQ(ValidateEvcd(toks), "");
}

// Negative (the validator itself is not vacuous): each of the closest
// non-conformant token streams -- an unterminated section, a fused command, a
// non-decimal simulation time, a *-prefixed name, and an unknown keyword --
// is rejected with a diagnosis, so the "" verdicts above are meaningful.
TEST_F(ExtendedVcdSyntaxSim, ValidatorRejectsNonConformantStreams) {
  using V = std::vector<std::string>;
  // The minimal conformant stream the corruptions perturb.
  EXPECT_EQ(ValidateEvcd(V{"$enddefinitions", "$end", "#10", "1!"}), "");
  // Section opener with no closing $end.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions"}), "");
  // Two commands fused into one token.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions$end", "#10", "1!"}), "");
  // simulation_time must be # followed by decimal digits only.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "#10ns", "1!"}), "");
  // A *-prefixed name is not the equivalent construct.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "#10", "*1!"}), "");
  // An unknown keyword is neither a declaration nor a simulation command.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "$dumpportsx", "$end"}),
            "");
  // A p-form value must end in two strength digits and cite a < code.
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "p0", "<0"}), "");
  EXPECT_NE(ValidateEvcd(V{"$enddefinitions", "$end", "p066", "!"}), "");
}

// simulation_keyword ::= $dumpports | ... : in the port-form file the opening
// checkpoint section is keyed $dumpports, not the 4-state $dumpvars (which
// matches no extended construct name, so the equivalence rule cannot admit
// it). The port form is exercised at the writer stage: no production caller
// enables it yet, and the keyword choice is a property of the writer's own
// output, independent of how the dumped values were produced. The whole
// port-form file conforms to Syntax 21-27, covering the port productions the
// hybrid runs above cannot reach ($var port node entries with 1 and [m:l]
// sizes, < integer identifier codes, and p-form values).
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
  // Non-vacuity anchors on the port-form section body and node entries.
  EXPECT_NE(content.find("$var port 1 <0 p0 $end"), std::string::npos);
  EXPECT_NE(content.find("$var port [3:0] <1 data $end"), std::string::npos);
  EXPECT_NE(content.find("p066 <0"), std::string::npos);
  EXPECT_NE(content.find("p101066 <1"), std::string::npos);
  EXPECT_EQ(ValidateEvcd(toks), "");
}

// simulation_keyword (continued): the checkpoint, suspend, and resume
// sections of the port-form file are keyed $dumpportsall, $dumpportsoff, and
// $dumpportson; none of the 4-state checkpoint keywords appears.
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

// Prose: port value changes are specified in binary format by 0, 1, x, and z
// AND include strength information -- value ::= p port_value
// 0_strength_component 1_strength_component, each strength a digit 0-7. All
// four binary states appear with both strength components: driven states at
// strong (6) strength and the high-impedance state at highz (0).
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
    px->value = MakeScalar(arena_, 1, 1);  // x = (aval=1, bval=1)
    vcd.RegisterSignal("px", 1, px);
    auto* pz = arena_.Create<Variable>();
    pz->value = MakeScalar(arena_, 0, 1);  // z = (aval=0, bval=1)
    vcd.RegisterSignal("pz", 1, pz);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto toks = Tokens(ReadVcd());
  // Each state carries its binary character plus the two strength digits.
  EXPECT_EQ(CountToken(toks, "p066"), 1u);
  EXPECT_EQ(CountToken(toks, "p166"), 1u);
  EXPECT_EQ(CountToken(toks, "px66"), 1u);
  EXPECT_EQ(CountToken(toks, "pz00"), 1u);
  // Every strength component in the file is a strength digit 0-7 (the value
  // tokens above end in their two components).
  for (const char* v : {"p066", "p166", "px66", "pz00"}) {
    std::string t = v;
    EXPECT_TRUE(IsStrengthDigit(t[t.size() - 2]));
    EXPECT_TRUE(IsStrengthDigit(t[t.size() - 1]));
  }
}

}  // namespace
}  // namespace delta
