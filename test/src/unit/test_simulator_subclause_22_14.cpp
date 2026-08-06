#include <unistd.h>

#include <filesystem>
#include <fstream>

#include "helpers_preprocess_and_get.h"

namespace fs = std::filesystem;

// Scratch directory holding an included source file, removed on destruction.
struct KeywordSimIncludeDir {
  fs::path dir;

  KeywordSimIncludeDir() {
    dir = fs::temp_directory_path() /
          ("delta_kwsim_22_14_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~KeywordSimIncludeDir() { fs::remove_all(dir); }

  void Write(const std::string& name, const std::string& content) {
    std::ofstream ofs(dir / name);
    ofs << content;
  }
};

// §22.14: the directives only pick the reserved word list; they do not change
// the semantics of the code they enclose. The 1364-2001 spelling of this
// design (`reg`, and `logic` used as an ordinary net name) computes the same
// value the unguarded 1800-2023 spelling does. The unguarded arm doubles as
// the runtime witness that, with no `begin_keywords anywhere, the
// implementation's default reserved word list is what applies.
TEST(KeywordVersionSimulation, KeywordRegionDoesNotChangeComputedValue) {
  auto guarded = PreprocessAndGet(
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire logic;\n"
      "  reg [15:0] result;\n"
      "  initial result = 16'd7 * 16'd6 + 16'd1;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(guarded, 43u);

  auto plain = PreprocessAndGet(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = 16'd7 * 16'd6 + 16'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(plain, guarded);
}

// §22.14: under a version that does not reserve it, the word is an ordinary
// identifier wherever an identifier may appear — including as an operand in an
// expression, which no earlier declaration-position test reaches. Here `logic`
// names a net under 1364-2001, is driven, and is then read back inside an
// arithmetic expression, so the value observed at the end of the run is what
// shows the word carried a real signal rather than merely parsing.
TEST(KeywordVersionSimulation, OldVersionIdentifierIsAnExpressionOperand) {
  auto result = PreprocessAndGet(
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire [7:0] logic;\n"
      "  reg [7:0] result;\n"
      "  assign logic = 8'd5;\n"
      "  initial #1 result = logic * 8'd3 + 8'd2;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 17u);
}

// §22.14: nested pairs are stacked, and `end_keywords returns to the specifier
// in effect before the matching `begin_keywords. The inner module is written
// against 1364-2001 and the outer against the enclosing 1800-2012 region; both
// elaborate and run together, and the instantiated inner module drives the
// value the outer one reports.
TEST(KeywordVersionSimulation, NestedRegionsSimulate) {
  auto result = PreprocessAndGet(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "module inner (output reg [7:0] o);\n"
      "  wire logic;\n"
      "  initial o = 8'd21;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  inner i (.o(result));\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 21u);
}

// §22.14: the region a `begin_keywords opens covers all source that follows,
// including source that arrives from another file, until the matching
// `end_keywords. The directive is in the top file and the module it governs is
// in an included one, where `logic` names a net — something only the 1364-2001
// list permits. The design elaborates and runs, so the region really did reach
// across the file boundary rather than merely surviving as preprocessor state.
TEST(KeywordVersionSimulation, RegionReachesIntoIncludedFile) {
  KeywordSimIncludeDir tmp;
  tmp.Write("driver.svh",
            "module driver (output reg [7:0] o);\n"
            "  wire logic;\n"
            "  initial o = 8'd57;\n"
            "endmodule\n");

  SimFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`begin_keywords \"1364-2001\"\n"
                           "`include \"driver.svh\"\n"
                           "`end_keywords\n"
                           "module t;\n"
                           "  logic [7:0] result;\n"
                           "  driver d (.o(result));\n"
                           "endmodule\n");

  PreprocConfig config;
  config.include_dirs.push_back(tmp.dir.string());
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  auto result = RunPreprocessedSim(f, fid, "result", pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result, 57u);
}
