#include <string>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.2.3: the keyword commands of the 4-state VCD file. The general
// information is presented as keyword-delimited sections; the declaration
// keywords describe the dump ($comment, $date, $enddefinitions, $scope,
// $timescale, $upscope, $var, $version) and the simulation keywords delimit
// the value checkpoints ($dumpall, $dumpoff, $dumpon, $dumpvars). Rules whose
// behavior depends on how the dumped object or the $dumpfile call is written
// in the source are driven through the full pipeline (parse, elaborate,
// lower, run) and observed in the dump file; only writer-confined formatting
// rules use the writer directly.
class VcdKeywordCommandsE2E : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents, mirroring the driver's registration
  // sequence (header, module scope, one registration per model variable,
  // $enddefinitions). Identifier codes ascend from '!' in name order.
  std::string RunVcd(const std::string& src, const std::string& scope = "t") {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope(scope);
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
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }

  // Runs the source (executing its $dumpfile call, which records the
  // unevaluated filename literal), then writes the header from what the run
  // captured. Mirrors a driver that opens the dump once $dumpfile has named
  // it. Returns the file contents; *resolved_name receives the evaluated
  // filename when non-null.
  std::string HeaderAfterRun(const std::string& src,
                             std::string* resolved_name = nullptr) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
    if (resolved_name != nullptr) *resolved_name = f.ctx.GetDumpFileName();
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns", f.ctx.GetDumpFileLiteral());
      vcd.EndDefinitions();
    }
    return ReadVcd();
  }
};

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

size_t CountLine(const std::vector<std::string>& lines,
                 std::string_view target) {
  size_t n = 0;
  for (const auto& l : lines) {
    if (l == target) ++n;
  }
  return n;
}

std::vector<std::string> Tokens(const std::string& line) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : line) {
    if (c == ' ') {
      if (!cur.empty()) out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

// The $var declaration line whose reference name is `name` ($var var_type
// size identifier_code reference $end), or an empty line when absent.
std::string FindVarLine(const std::vector<std::string>& lines,
                        std::string_view name) {
  for (const auto& l : lines) {
    auto toks = Tokens(l);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) return l;
  }
  return {};
}

// The body of the section opened by `keyword`, up to (not including) the next
// $end. Empty when the keyword is absent.
std::string Section(const std::string& content, std::string_view keyword) {
  auto start = content.find(keyword);
  if (start == std::string::npos) return {};
  auto end = content.find("$end", start);
  if (end == std::string::npos) return content.substr(start);
  return content.substr(start, end - start);
}

// §21.7.2.3 (intro + Table 21-10): the general information is presented as
// keyword-delimited sections, and $enddefinitions marks the end of the header
// information and definitions -- every declaration section precedes it and no
// declaration keyword follows it. The header, scope, and variable sections
// come from a real module driven through the whole pipeline.
TEST_F(VcdKeywordCommandsE2E, DeclarationSectionsEndAtEnddefinitions) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    $dumpvars;\n"
      "    #1 a = 1;\n"
      "  end\n"
      "endmodule\n");
  for (const char* kw :
       {"$date", "$version", "$timescale", "$scope", "$var", "$upscope"}) {
    auto pos = content.find(kw);
    ASSERT_NE(pos, std::string::npos) << kw;
    // Each declaration section closes with $end...
    EXPECT_NE(content.find("$end", pos), std::string::npos) << kw;
    // ...and sits before the $enddefinitions boundary.
    EXPECT_LT(pos, content.find("$enddefinitions")) << kw;
  }
  // Past the boundary only simulation commands appear: no declaration keyword
  // may follow $enddefinitions.
  auto sim = content.substr(content.find("$enddefinitions"));
  EXPECT_EQ(sim.find("$var "), std::string::npos);
  EXPECT_EQ(sim.find("$scope "), std::string::npos);
  EXPECT_EQ(sim.find("$upscope"), std::string::npos);
  // The $timescale section carries the timescale the simulation ran with.
  EXPECT_NE(Section(content, "$timescale").find("1ns"), std::string::npos);
}

// §21.7.2.3: the $date section indicates the date on which the VCD file was
// generated. The stamp comes from the writer's own clock, so the section body
// must carry an actual date (a four-digit year), not a fixed banner. Date
// production is confined to the writer and independent of the model, so the
// writer is driven directly.
TEST_F(VcdKeywordCommandsE2E, DateSectionCarriesGenerationDate) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
  }
  auto date = Section(ReadVcd(), "$date");
  ASSERT_FALSE(date.empty());
  // A generation date names a 20xx year; the negative form -- a dateless
  // banner -- carries no such year and must not appear.
  EXPECT_NE(date.find(", 20"), std::string::npos) << date;
  EXPECT_EQ(date.find("Generated by"), std::string::npos) << date;
}

// §21.7.2.3: the scope type of a $scope section indicates the kind of scope --
// module (module instances), task, function, begin (named sequential block),
// or fork (named parallel block). The kind-to-keyword mapping is confined to
// the writer, so each kind is checked directly; no other spelling (and no
// keyword from a different kind) may be substituted.
TEST_F(VcdKeywordCommandsE2E, ScopeKeywordIndicatesScopeKind) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("m1", VcdScopeKind::kModule);
    vcd.BeginScope("t1", VcdScopeKind::kTask);
    vcd.BeginScope("f1", VcdScopeKind::kFunction);
    vcd.BeginScope("b1", VcdScopeKind::kBegin);
    vcd.BeginScope("fk1", VcdScopeKind::kFork);
    for (int i = 0; i < 5; ++i) vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto lines = Lines(ReadVcd());
  EXPECT_TRUE(HasLine(lines, "$scope module m1 $end"));
  EXPECT_TRUE(HasLine(lines, "$scope task t1 $end"));
  EXPECT_TRUE(HasLine(lines, "$scope function f1 $end"));
  EXPECT_TRUE(HasLine(lines, "$scope begin b1 $end"));
  EXPECT_TRUE(HasLine(lines, "$scope fork fk1 $end"));
  // §21.7.2.3: each $scope is closed by an $upscope returning to the next
  // higher level, so the five openings balance with five $upscope sections.
  EXPECT_EQ(CountLine(lines, "$upscope $end"), 5u);
}

// §21.7.2.3: a module scope in the model is recorded with the module scope
// type, and $upscope returns to the next higher level -- observed from a real
// module driven through the pipeline.
TEST_F(VcdKeywordCommandsE2E, ModuleScopeFromRealModuleUsesModuleKeyword) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial a = 0;\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "$scope module t $end"));
  EXPECT_TRUE(HasLine(lines, "$upscope $end"));
  // The scope opens before its variables and closes after them, before the
  // definitions end.
  EXPECT_LT(content.find("$scope module t $end"), content.find("$var "));
  EXPECT_LT(content.find("$var "), content.find("$upscope $end"));
  EXPECT_LT(content.find("$upscope $end"), content.find("$enddefinitions"));
  // Negative form: a module construct is indicated only by the module
  // keyword, never by one of the other four scope types.
  EXPECT_EQ(content.find("$scope task"), std::string::npos);
  EXPECT_EQ(content.find("$scope function"), std::string::npos);
  EXPECT_EQ(content.find("$scope begin"), std::string::npos);
  EXPECT_EQ(content.find("$scope fork"), std::string::npos);
}

// §21.7.2.3: the $var section prints the name and identifier code of each
// dumped variable; the size gives how many bits are in the variable, and the
// identifier (the reference) is the variable's name in the model. Declared
// widths of 1, 8, and 16 bits from real declarations must each be reflected
// in the size field, and the identifier code is a printable-ASCII code.
TEST_F(VcdKeywordCommandsE2E, VarSectionPrintsSizeIdentifierCodeAndReference) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  logic [15:0] w;\n"
      "  initial begin s = 0; v = 8'd1; w = 16'd2; end\n"
      "endmodule\n");
  auto lines = Lines(content);
  struct Case {
    const char* name;
    const char* size;
  };
  for (const auto& c :
       std::initializer_list<Case>{{"s", "1"}, {"v", "8"}, {"w", "16"}}) {
    auto line = FindVarLine(lines, c.name);
    ASSERT_FALSE(line.empty()) << c.name;
    auto toks = Tokens(line);
    EXPECT_EQ(toks[2], c.size) << line;     // size = bits in the variable
    ASSERT_EQ(toks[3].size(), 1u) << line;  // one identifier-code character
    EXPECT_GE(toks[3][0], '!') << line;     // printable ASCII code
    EXPECT_LE(toks[3][0], '~') << line;
    EXPECT_EQ(toks[4], c.name) << line;  // reference = model name
    EXPECT_EQ(toks[5], "$end") << line;
  }
}

// §21.7.2.3: the $var size and the $dumpvars initial value also hold for a
// variable produced by a declaration initializer rather than a procedural
// assignment -- the declared width drives the size field and the initializer
// supplies the initial value the $dumpvars section lists.
TEST_F(VcdKeywordCommandsE2E, VarFromDeclarationInitializer) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v = 8'd5;\n"
      "  initial $dumpvars;\n"
      "endmodule\n");
  auto line = FindVarLine(Lines(content), "v");
  ASSERT_FALSE(line.empty()) << content;
  EXPECT_EQ(Tokens(line)[2], "8") << line;  // size = declared bit count
  // The initializer's value is what $dumpvars records as the initial value.
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("b101 !"), std::string::npos) << dumpvars;
}

// §21.7.2.3 (shall): in the $var section a net of net type uwire shall have a
// var_type of wire. The net type comes from the real declaration -- a scalar
// and a vector uwire net both flow through elaboration and lowering into the
// registration -- and the uwire keyword itself never appears as a var_type.
TEST_F(VcdKeywordCommandsE2E, UwireNetVarTypeIsWire) {
  auto content = RunVcd(
      "module t;\n"
      "  uwire u;\n"
      "  uwire [3:0] uv;\n"
      "  logic d;\n"
      "  assign u = d;\n"
      "  assign uv = {d, d, d, d};\n"
      "  initial begin d = 0; #1 d = 1; end\n"
      "endmodule\n");
  auto lines = Lines(content);
  auto u_line = FindVarLine(lines, "u");
  ASSERT_FALSE(u_line.empty()) << content;
  EXPECT_EQ(Tokens(u_line)[1], "wire") << u_line;
  auto uv_line = FindVarLine(lines, "uv");
  ASSERT_FALSE(uv_line.empty()) << content;
  EXPECT_EQ(Tokens(uv_line)[1], "wire") << uv_line;
  EXPECT_EQ(Tokens(uv_line)[2], "4") << uv_line;
  // Negative form: the uwire spelling never reaches the file as a var_type.
  EXPECT_EQ(content.find("uwire"), std::string::npos);
}

// §21.7.2.3: the $version section indicates the version of the VCD writer and
// the $dumpfile system task used to create the file. A string-literal
// filename is reproduced, quotes and all, inside the $dumpfile(...) entry of
// the $version section -- driven by a real $dumpfile call.
TEST_F(VcdKeywordCommandsE2E, VersionReproducesStringLiteralDumpfile) {
  auto content = HeaderAfterRun(
      "module t;\n"
      "  initial $dumpfile(\"dump1.dump\");\n"
      "endmodule\n");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  EXPECT_NE(version.find("DeltaHDL"), std::string::npos) << version;
  EXPECT_NE(version.find("$dumpfile(\"dump1.dump\")"), std::string::npos)
      << version;
}

// §21.7.2.3 (shall): when a variable specifies the filename within $dumpfile,
// the unevaluated variable literal shall appear in the $version string. The
// variable is declared and assigned in real source; the run resolves the
// filename to the variable's value, yet $version shows the variable name and
// not that value.
TEST_F(VcdKeywordCommandsE2E, VersionKeepsVariableFilenameUnevaluated) {
  std::string resolved;
  auto content = HeaderAfterRun(
      "module t;\n"
      "  string fn;\n"
      "  initial begin\n"
      "    fn = \"resolved_name.vcd\";\n"
      "    $dumpfile(fn);\n"
      "  end\n"
      "endmodule\n",
      &resolved);
  // The run really evaluated the variable for the file name...
  EXPECT_EQ(resolved, "resolved_name.vcd");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  // ...but the $version entry carries the unevaluated variable literal.
  EXPECT_NE(version.find("$dumpfile(fn)"), std::string::npos) << version;
  // Negative form: the evaluated value must not replace the literal.
  EXPECT_EQ(content.find("resolved_name"), std::string::npos) << content;
}

// §21.7.2.3 (shall): when an expression specifies the filename, the
// unevaluated expression literal appears in $version. A concatenation of two
// string literals resolves to their joined value, yet $version reproduces the
// expression form rather than the resolved name.
TEST_F(VcdKeywordCommandsE2E, VersionKeepsExpressionFilenameUnevaluated) {
  auto content = HeaderAfterRun(
      "module t;\n"
      "  initial $dumpfile({\"part1\", \".vcd\"});\n"
      "endmodule\n");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  EXPECT_NE(version.find("$dumpfile({\"part1\",\".vcd\"})"), std::string::npos)
      << version;
  // Negative form: the evaluated concatenation must not appear.
  EXPECT_EQ(content.find("part1.vcd"), std::string::npos) << content;
}

// §21.7.2.3 (shall): a parameter naming the file is likewise an expression
// specifying the filename, so its unevaluated identifier -- not the constant
// it resolves to -- appears in the $version string.
TEST_F(VcdKeywordCommandsE2E, VersionKeepsParameterFilenameUnevaluated) {
  auto content = HeaderAfterRun(
      "module t;\n"
      "  parameter string P = \"param_name.vcd\";\n"
      "  initial $dumpfile(P);\n"
      "endmodule\n");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  EXPECT_NE(version.find("$dumpfile(P)"), std::string::npos) << version;
  // Negative form: the parameter's constant value must not replace it.
  EXPECT_EQ(content.find("param_name"), std::string::npos) << content;
}

// §21.7.2.3 (shall): a localparam naming the file takes the same
// constant-identifier path as a parameter, and its unevaluated identifier is
// what $version shows.
TEST_F(VcdKeywordCommandsE2E, VersionKeepsLocalparamFilenameUnevaluated) {
  auto content = HeaderAfterRun(
      "module t;\n"
      "  localparam string LP = \"local_name.vcd\";\n"
      "  initial $dumpfile(LP);\n"
      "endmodule\n");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  EXPECT_NE(version.find("$dumpfile(LP)"), std::string::npos) << version;
  // Negative form: the localparam's constant value must not replace it.
  EXPECT_EQ(content.find("local_name"), std::string::npos) << content;
}

// §21.7.2.3 (shall): a function call is an expression specifying the
// filename, so $version reproduces the call form -- callee and parentheses --
// rather than the string the call returned at run time.
TEST_F(VcdKeywordCommandsE2E, VersionKeepsFunctionCallFilenameUnevaluated) {
  std::string resolved;
  auto content = HeaderAfterRun(
      "module t;\n"
      "  function string mkname();\n"
      "    return \"fn_name.vcd\";\n"
      "  endfunction\n"
      "  initial $dumpfile(mkname());\n"
      "endmodule\n",
      &resolved);
  // The run really called the function to resolve the filename...
  EXPECT_EQ(resolved, "fn_name.vcd");
  auto version = Section(content, "$version");
  ASSERT_FALSE(version.empty()) << content;
  // ...but the $version entry carries the unevaluated call expression.
  EXPECT_NE(version.find("$dumpfile(mkname())"), std::string::npos) << version;
  // Negative form: the returned string must not replace the call form.
  EXPECT_EQ(content.find("fn_name"), std::string::npos) << content;
}

// §21.7.2.3: the $dumpfile entry is reproduced in $version only when a
// $dumpfile call supplied a filename. With no such call the gating condition
// is false and $version carries no $dumpfile entry.
TEST_F(VcdKeywordCommandsE2E, VersionOmitsDumpfileWithoutCall) {
  auto content = HeaderAfterRun(
      "module t;\n"
      "  logic a;\n"
      "  initial a = 0;\n"
      "endmodule\n");
  EXPECT_NE(content.find("$version"), std::string::npos);
  EXPECT_EQ(content.find("$dumpfile("), std::string::npos);
}

// §21.7.2.3: the $comment section provides the means of inserting a comment
// in the VCD file, whether the text is a single line or spans several lines;
// each comment section is closed by its own $end. The section form is
// confined to the writer (the text originates from the dumper itself), so the
// writer is driven directly.
TEST_F(VcdKeywordCommandsE2E, CommentSectionDelimitsSingleAndMultiLineText) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.WriteComment("a single-line comment");
    vcd.WriteComment("first line\nsecond line");
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  auto first = content.find("$comment");
  ASSERT_NE(first, std::string::npos);
  auto first_end = content.find("$end", first);
  ASSERT_NE(first_end, std::string::npos);
  EXPECT_NE(
      content.substr(first, first_end - first).find("a single-line comment"),
      std::string::npos);
  auto second = content.find("$comment", first_end);
  ASSERT_NE(second, std::string::npos);
  auto second_end = content.find("$end", second);
  ASSERT_NE(second_end, std::string::npos);
  auto body = content.substr(second, second_end - second);
  // The multiple-line text survives intact, line break included.
  EXPECT_NE(body.find("first line\nsecond line"), std::string::npos) << body;
}

// §21.7.2.3: the simulation keyword sections and their value lists --
// $dumpvars lists the initial values of all variables dumped, $dumpoff
// indicates all variables dumped with x values, $dumpon lists the current
// values on resumption, and $dumpall specifies the current values of all
// variables. The checkpoints are produced by the corresponding system tasks
// in real source (§21.7.1.2 through §21.7.1.4 machinery); this test observes
// that each section covers every dumped variable with the value form the
// keyword implies. Identifier codes: 'a' -> ! and 'v' -> " (name order).
TEST_F(VcdKeywordCommandsE2E, SimulationKeywordSectionsListDumpedValues) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 0; v = 4'd3;\n"
      "    $dumpvars;\n"
      "    #1 a = 1;\n"
      "    #1 $dumpoff;\n"
      "    #1 $dumpon;\n"
      "    #1 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("0!"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("b11 \""), std::string::npos) << dumpvars;
  auto dumpoff = Section(content, "$dumpoff");
  ASSERT_FALSE(dumpoff.empty()) << content;
  EXPECT_NE(dumpoff.find("x!"), std::string::npos) << dumpoff;
  EXPECT_NE(dumpoff.find("bx \""), std::string::npos) << dumpoff;
  auto dumpon = Section(content, "$dumpon");
  ASSERT_FALSE(dumpon.empty()) << content;
  EXPECT_NE(dumpon.find("1!"), std::string::npos) << dumpon;
  EXPECT_NE(dumpon.find("b11 \""), std::string::npos) << dumpon;
  auto dumpall = Section(content, "$dumpall");
  ASSERT_FALSE(dumpall.empty()) << content;
  EXPECT_NE(dumpall.find("1!"), std::string::npos) << dumpall;
  EXPECT_NE(dumpall.find("b11 \""), std::string::npos) << dumpall;
}

// §21.7.2.3: the $dumpvars section lists the initial values of the variables
// dumped -- and which variables those are follows the selection the source's
// $dumpvars call made. A call naming one individual variable produces a
// section that records that variable's initial value and nothing for the
// unselected variable (identifier codes: 'a' -> ! and 'v' -> ").
TEST_F(VcdKeywordCommandsE2E, DumpvarsSectionCoversOnlySelectedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    a = 0; v = 4'd3;\n"
      "    $dumpvars(0, a);\n"
      "  end\n"
      "endmodule\n");
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("0!"), std::string::npos) << dumpvars;
  // Negative form: the unselected variable contributes no record -- its
  // identifier code never appears inside the section.
  EXPECT_EQ(dumpvars.find('"'), std::string::npos) << dumpvars;
}

}  // namespace
}  // namespace delta
