// §34.4 Protect pragma directives -- what the design is once they are read.
//
// Two of the subclause's rules make a claim about text that the preprocessor's
// own state cannot settle. A protected envelope is a lexical region, and the
// scope those directives take effect over is attached to no declarative region
// and to no declaration. Both say something about where a region begins and
// ends and nothing about what the text inside it becomes: the design written
// among the directives is still the design, whichever declaration the
// directives happen to have been written in and whichever file they came from.
//
// That is only visible past the preprocessor, so every design here is real
// source driven through the whole preprocess -> parse -> elaborate -> lower ->
// simulate pipeline, and what is read at the end is the value the design
// computes. A directive read as anything other than a lexical mark -- a line
// swallowed, a declaration cut short at an envelope boundary, a keyword left
// in the text for the lexer to find -- costs the run its value or its
// elaboration, so the value arriving is the observation.
//
// The directives are written as the real `pragma syntax of §22.11, and the
// runs that cross a file boundary use the real `include syntax of §22.4 with
// the file on disk, so nothing here is assembled from an intermediate the
// pipeline would not have built for itself.

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

#include "helpers_preprocess_and_get.h"

namespace fs = std::filesystem;

namespace {

// Runs a source text through the whole pipeline and keeps the value of
// `result`, which every design below declares outside every protected region
// and assigns inside one. A design that lost a line to a directive answers
// with the value it started at rather than the one it computes.
struct DesignRun {
  SimFixture f;
  Preprocessor pp{f.mgr, f.diag, {}};
  uint64_t result = 0;

  explicit DesignRun(const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile("<test>", src), "result", pp);
  }

  // The same, for a design that has to sit at a path of its own because it
  // reaches for a file beside it.
  DesignRun(const std::string& path, const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile(path, src), "result", pp);
  }
};

// A directory holding the half of a design that an `include reaches for. Each
// test names its own, so two of them running at once never meet in the same
// place.
struct IncludeTestDir {
  fs::path dir;

  explicit IncludeTestDir(const std::string& name) {
    dir = fs::temp_directory_path() / ("delta_protect_sim_34_04_" + name);
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  // Writes the half of the design that lives in the included file, and hands
  // back the path the other half has to be registered under for the inclusion
  // to resolve beside it.
  std::string WriteBody(const std::string& content) {
    std::ofstream ofs(dir / "body.svh");
    ofs << content;
    return (dir / "top.sv").string();
  }
};

// ---------------------------------------------------------------------------
// A region is lexical, so it neither ends where a declaration ends nor takes
// the declaration with it.
// ---------------------------------------------------------------------------

// A region opened among a module's declarations and closed after the module
// has ended. The region running past the module's end leaves the module whole,
// so the design elaborates and the code inside the region is code of that
// module like any other.
TEST(ProtectPragmaDirectivesSimulation, ARegionMayCloseAfterTheModuleEnds) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "endmodule\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The other way round: the region opens before the module and closes among its
// declarations. Neither delimiter is where the module begins or ends, and the
// module is what runs.
TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenBeforeTheModuleBegins) {
  DesignRun run(
      "`pragma protect begin\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// A region spanning two declarations. It opens in the first module and closes
// in the second, so no declarative region contains it, and both modules are
// still there for elaboration to find.
TEST(ProtectPragmaDirectivesSimulation, ARegionMaySpanTwoModules) {
  DesignRun run(
      "module a;\n"
      "`pragma protect begin\n"
      "  int unused = 7;\n"
      "endmodule\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The smallest declarative region a delimiter can stand in. Opening a region
// inside a named block and closing it outside leaves the block, the module and
// the statement between them intact.
TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenInsideANamedBlock) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "  initial begin : blk\n"
      "`pragma protect begin\n"
      "    result = 42;\n"
      "  end\n"
      "endmodule\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// ---------------------------------------------------------------------------
// The describing directives contribute nothing to the design.
// ---------------------------------------------------------------------------

// Every shape a pragma expression may take, written among the declarations of
// a running design: keywords standing alone, keywords carrying a string, an
// identifier and a number, a keyword whose value is a list of further
// expressions, and several keywords sharing one directive. All of them are
// read as descriptions of the envelope and none of them reaches the design, so
// the value is the one the design alone accounts for.
TEST(ProtectPragmaDirectivesSimulation, DescribingKeywordsReachNoDesign) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme\", author_info=\"IP group\"\n"
      "`pragma protect encoding=(enctype=\"raw\", bytes=190)\n"
      "`pragma protect data_method=des_cbc\n"
      "`pragma protect comment=1997\n"
      "`pragma protect data_public_key\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "`pragma protect reset\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// The negative that pairs with it. A directive naming another specification is
// no protect pragma directive, so it delimits nothing -- and the pragma
// mechanism still consumes it, leaving the design between two of them running
// exactly as the design between two protect directives does.
TEST(ProtectPragmaDirectivesSimulation, ADirectiveOfAnotherPragmaDelimitsNone) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma acme_tool begin\n"
      "  initial result = 42;\n"
      "`pragma acme_tool end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// ---------------------------------------------------------------------------
// The scope reaches across a file boundary, and so does a region.
// ---------------------------------------------------------------------------

// A region opened in the file the reading started in and closed in the file it
// includes. The design is split over the same boundary, and what runs is one
// design rather than the two texts it was written as.
TEST(ProtectPragmaDirectivesSimulation, ARegionMayCloseInsideAnIncludedFile) {
  IncludeTestDir tmp("region_into_include");
  std::string body =
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  std::string src =
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`include \"body.svh\"\n";

  DesignRun run(tmp.WriteBody(body), src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

// And a region opened in an included file and closed after the inclusion has
// returned, so neither delimiter is the one that has to stand in the outer
// file for the design to survive the crossing.
TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenInsideAnIncludedFile) {
  IncludeTestDir tmp("region_out_of_include");
  std::string body =
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n";
  std::string src =
      "`include \"body.svh\"\n"
      "`pragma protect end\n"
      "endmodule\n";

  DesignRun run(tmp.WriteBody(body), src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
