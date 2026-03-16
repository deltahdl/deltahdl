#include <cstdlib>
#include <filesystem>
#include <fstream>

#include "fixture_simulator.h"
#include "preprocessor/preprocessor.h"
#include "simulator/variable.h"

using namespace delta;
namespace fs = std::filesystem;

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

static uint64_t PreprocessAndGet(IncludeTestDir& tmp,
                                 const std::string& main_src,
                                 const char* var_name) {
  SimFixture f;
  tmp.WriteFile("main.sv", main_src);
  auto fid = f.mgr.AddFile((tmp.dir / "main.sv").string(), main_src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto fid2 = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

TEST(IncludeFileSimulation, IncludedMacroValueSimulatesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("constants.svh", "`define MAGIC 8'd42\n");

  auto result = PreprocessAndGet(tmp,
      "`include \"constants.svh\"\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `MAGIC;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(IncludeFileSimulation, NestedIncludeMacroSimulatesCorrectly) {
  IncludeTestDir tmp;
  tmp.WriteFile("base.svh", "`define BASE 8'd10\n");
  tmp.WriteFile("derived.svh",
                "`include \"base.svh\"\n"
                "`define DERIVED (`BASE + 8'd5)\n");

  auto result = PreprocessAndGet(tmp,
      "`include \"derived.svh\"\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `DERIVED;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}

TEST(IncludeFileSimulation, MultipleIncludesContributeToSimulation) {
  IncludeTestDir tmp;
  tmp.WriteFile("val_a.svh", "`define A 8'd3\n");
  tmp.WriteFile("val_b.svh", "`define B 8'd7\n");

  auto result = PreprocessAndGet(tmp,
      "`include \"val_a.svh\"\n"
      "`include \"val_b.svh\"\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `A + `B;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}
