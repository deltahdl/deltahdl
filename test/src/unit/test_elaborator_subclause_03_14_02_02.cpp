#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

constexpr const char* kLibMap = "library rtlLib src/*.sv;\n";

RtlirDesign* CompileCommandLineAndElaborate(CommandLineHarness& h,
                                            const ScratchDir& tmp,
                                            const std::vector<fs::path>& files,
                                            std::string_view top) {
  if (!h.libs.LoadMapFile(tmp.dir / "lib.map")) return nullptr;
  if (!h.compiler.CompileCommandLine(files, h.unit)) return nullptr;
  Elaborator elab(h.arena, h.diag, &h.unit);
  return elab.Elaborate(top);
}

const RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

TEST(SinglePassCompileTimescale, ACompilationUnitTimeunitReachesTheDesign) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto src = tmp.Write("src/top.sv",
                       "timeunit 100ps;\n"
                       "module top;\n"
                       "  timeprecision 1ps;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {src}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(design->cu_timescale.magnitude, 100);
}

TEST(SinglePassCompileTimescale,
     ACompilationUnitTimeprecisionReachesTheDesign) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto src = tmp.Write("src/top.sv",
                       "timeprecision 10ps;\n"
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {src}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(design->cu_timescale.prec_magnitude, 10);
}

TEST(SinglePassCompileTimescale,
     ATimeunitInOneFileSetsTheFallbackForAModuleInAnother) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cu = tmp.Write("src/cu.sv", "timeunit 100ps;\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  timeprecision 1ps;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {cu, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.magnitude, 100);
}

TEST(SinglePassCompileTimescale,
     ACompilationUnitPrecisionEntersTheGlobalPrecisionSearch) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cu = tmp.Write("src/cu.sv", "timeprecision 10ps;\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {cu, top}, "");
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->global_time_precision, TimeUnit::kPs);
}

constexpr const char* kFirstFileTimeunitPs = "timeunit 1ps;\n";
constexpr const char* kFirstFileTimeprecisionPs = "timeprecision 1ps;\n";

std::vector<fs::path> TwoFileCommandLine(ScratchDir& tmp, const char* first,
                                         const char* second) {
  tmp.Write("lib.map", kLibMap);
  return {tmp.Write("src/first.sv", first), tmp.Write("src/second.sv", second)};
}

void CompileTwoFileCommandLine(CommandLineHarness& h, const ScratchDir& tmp,
                               const std::vector<fs::path>& files) {
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  h.compiler.CompileCommandLine(files, h.unit);
}

TEST(SinglePassCompileTimescale,
     ConflictingCompilationUnitTimeunitsAcrossFilesAreReported) {
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The later of the two declarations follows this line.\n"
      "timeunit 1ns;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeunit does not match prior declaration",
      LineHolding(kSecondFile, "timeunit 1ns;"), "3.14.2.2"));
}

TEST(SinglePassCompileTimescale,
     ConflictingCompilationUnitTimeprecisionsAcrossFilesAreReported) {
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The later of the two precision declarations follows this line.\n"
      "timeprecision 1ns;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeprecisionPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeprecision does not match prior declaration",
      LineHolding(kSecondFile, "timeprecision 1ns;"), "3.14.2.2"));
}

TEST(SinglePassCompileTimescale,
     AMatchingCompilationUnitTimeunitInASecondFileIsAccepted) {
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The repeat of the first file's declaration follows this line.\n"
      "timeunit 1ps;\n"
      "module top;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n";

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile), "");
  EXPECT_TRUE(h.diag.Diagnostics().empty());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->cu_timescale.unit, TimeUnit::kPs);
}

TEST(SinglePassCompileTimescale, ConflictingMagnitudesInOneUnitAreReported) {
  ScratchDir tmp;
  constexpr const char* kSecondFile =
      "// The declaration that differs in magnitude follows this line.\n"
      "timeunit 10ps;\n"
      "module top;\n"
      "endmodule\n";

  CommandLineHarness h;
  CompileTwoFileCommandLine(
      h, tmp, TwoFileCommandLine(tmp, kFirstFileTimeunitPs, kSecondFile));
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(), "timeunit does not match prior declaration",
      LineHolding(kSecondFile, "timeunit 10ps;"), "3.14.2.2"));
}
