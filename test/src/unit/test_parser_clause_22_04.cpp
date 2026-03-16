#include <cstdlib>
#include <filesystem>
#include <fstream>

#include "fixture_parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct IncludeTestDir {
  fs::path dir;
  IncludeTestDir() {
    dir =
        fs::temp_directory_path() / ("delta_test_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }
  ~IncludeTestDir() { fs::remove_all(dir); }
  fs::path WriteFile(const std::string& rel, const std::string& content) {
    auto full = dir / rel;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

static ParseResult ParseWithIncludes(IncludeTestDir& tmp,
                                     const std::string& main_src) {
  ParseResult result;
  DiagEngine diag(result.mgr);
  tmp.WriteFile("main.sv", main_src);
  auto fid =
      result.mgr.AddFile((tmp.dir / "main.sv").string(), main_src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.cu->default_nettype = preproc.DefaultNetType();
  result.cu->default_decay_time = preproc.DefaultDecayTime();
  result.cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.cu->default_trireg_strength = preproc.DefaultTriregStrength();
  result.cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.cu->delay_mode_directive = preproc.DelayModeDirective();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(IncludeFileParsing, IncludedModuleDefinitionParsesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("counter.svh",
                "module counter(\n"
                "  input clk,\n"
                "  output logic [7:0] count\n"
                ");\n"
                "  always_ff @(posedge clk) count <= count + 1;\n"
                "endmodule\n");

  auto r = ParseWithIncludes(tmp, "`include \"counter.svh\"\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "counter");
}

TEST(IncludeFileParsing, IncludedPortListProducesValidAST) {
  IncludeTestDir tmp;
  tmp.WriteFile("ports.svh", "input a, input b, output c\n");

  auto r = ParseWithIncludes(tmp,
                             "module m(\n"
                             "`include \"ports.svh\"\n"
                             ");\n"
                             "  assign c = a & b;\n"
                             "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(IncludeFileParsing, MultipleIncludedModulesParsed) {
  IncludeTestDir tmp;
  tmp.WriteFile("mod_a.svh", "module mod_a; endmodule\n");
  tmp.WriteFile("mod_b.svh", "module mod_b; endmodule\n");

  auto r = ParseWithIncludes(tmp,
                             "`include \"mod_a.svh\"\n"
                             "`include \"mod_b.svh\"\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(IncludeFileParsing, NestedIncludeProducesValidAST) {
  IncludeTestDir tmp;
  tmp.WriteFile("inner.svh", "parameter P = 42;\n");
  tmp.WriteFile("outer.svh", "`include \"inner.svh\"\n");

  auto r = ParseWithIncludes(tmp,
                             "module t;\n"
                             "`include \"outer.svh\"\n"
                             "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(IncludeFileParsing, IncludedMacroAffectsParseResult) {
  IncludeTestDir tmp;
  tmp.WriteFile("defs.svh", "`define WIDTH 8\n");

  auto r = ParseWithIncludes(tmp,
                             "`include \"defs.svh\"\n"
                             "module t;\n"
                             "  logic [`WIDTH-1:0] data;\n"
                             "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
