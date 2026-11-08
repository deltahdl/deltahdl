#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "driver/protect_license_libraries.h"
#include "fixture_scratch_dir.h"
#include "helpers_license_library.h"
#include "helpers_reported_error.h"
#include "parser/precompiled_library.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

struct RuntimeAsking {
  LicenseLibrary library;
  SourceManager mgr;
  DiagEngine diag{mgr};
  ProtectLicenseLibraries libraries;
  std::vector<ProtectRuntimeLicense> licenses;
  uint32_t file_id = mgr.AddFile("<recovered>", "\n\n\n\n");

  void Met(std::string_view feature, uint64_t match, uint32_t line) {
    licenses.push_back(
        {library.Asking(feature, match), SourceLoc{file_id, line, 1}});
  }

  bool Granted() { return RuntimeLicensesGranted(licenses, libraries, diag); }
};

TEST(ProtectRuntimeLicenseAsking, MatchingAnswersLetExecutionBegin) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  EXPECT_TRUE(asking.Granted());
  EXPECT_TRUE(asking.diag.Diagnostics().empty());
}

TEST(ProtectRuntimeLicenseAsking, AnotherAnswerKeepsExecutionFromBeginning) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  asking.Met("run", 42, 3);
  EXPECT_FALSE(asking.Granted());
}

TEST(ProtectRuntimeLicenseAsking, AnotherAnswerIsReportedWithItsValue) {
  RuntimeAsking asking;
  asking.Met("run", 42, 3);
  asking.Granted();
  EXPECT_TRUE(ReportedError(
      asking.diag.Diagnostics(),
      "protect pragma runtime_license entry function \"deltahdl_license_check\""
      " in \"" +
          asking.library.file +
          "\" returned 5 for feature \"run\", not the match value 42, so this "
          "tool is not licensed to execute the model",
      3, "34.5.29.2"));
}

TEST(ProtectRuntimeLicenseAsking, EachLicenceIsReleased) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  asking.Met("run", 42, 3);
  asking.Granted();
  asking.libraries.Release();
  EXPECT_EQ(asking.library.Released(), 2);
}

struct BindAsking {
  LicenseLibrary library;
  SourceManager mgr;
  DiagEngine diag{mgr};
  ProtectLicenseLibraries libraries;
  std::string dpl = (library.scratch.dir / "ip.dpl").string();

  void Precompiled(std::string_view feature) {
    PrecompiledDirectives directives;
    directives.runtime_licenses.push_back(library.Asking(feature, 42));
    ASSERT_TRUE(PrecompiledLibrary::Save("module sealed_m;\nendmodule\n", "ip",
                                         dpl, directives));
  }

  bool Granted() {
    return PrecompiledRuntimeLicensesGranted({dpl}, libraries, diag);
  }
};

TEST(ProtectRuntimeLicenseAsking, APrecompiledMatchingAnswerLetsTheBindRun) {
  BindAsking asking;
  asking.Precompiled("open");
  EXPECT_TRUE(asking.Granted());
  EXPECT_TRUE(asking.diag.Diagnostics().empty());
}

TEST(ProtectRuntimeLicenseAsking,
     APrecompiledOtherAnswerKeepsTheBindFromRunning) {
  BindAsking asking;
  asking.Precompiled("open");
  asking.Precompiled("run");
  EXPECT_FALSE(asking.Granted());
}

TEST(ProtectRuntimeLicenseAsking,
     APrecompiledOtherAnswerIsReportedWithItsValue) {
  BindAsking asking;
  asking.Precompiled("run");
  asking.Granted();
  EXPECT_TRUE(ReportedError(
      asking.diag.Diagnostics(),
      "protect pragma runtime_license entry function \"deltahdl_license_check\""
      " in \"" +
          asking.library.file +
          "\" returned 5 for feature \"run\", not the match value 42, so this "
          "tool is not licensed to execute the model",
      0, "34.5.29.2"));
}

TEST(ProtectRuntimeLicenseAsking, EachPrecompiledLicenceIsReleased) {
  BindAsking asking;
  asking.Precompiled("open");
  asking.Precompiled("run");
  asking.Granted();
  asking.libraries.Release();
  EXPECT_EQ(asking.library.Released(), 2);
}

TEST(ProtectRuntimeLicenseAsking, ThePrecompileKeepsTheLicenceItMet) {
  constexpr std::string_view kKey = "precompile-exchange-key";
  ScratchDir tmp;
  std::string authored = "module sealed_m;\n`pragma protect begin\n";
  authored += "`pragma protect runtime_license=(library=\"liblic.so\", ";
  authored += "entry=\"checkout\", feature=\"simulate\", match=7)\n";
  authored += "  int result = 1;\n`pragma protect end\nendmodule\n";
  std::string source = (tmp.dir / "sealed.sv").string();
  std::ofstream(source) << EncryptEnvelopes(authored, kKey);
  CliOptions opts;
  opts.source_files = {source};
  opts.precompile_library = "ip";
  opts.precompile_output = (tmp.dir / "ip.dpl").string();
  opts.protect.exchange_key = std::string(kKey);
  SourceManager mgr;
  DiagEngine diag{mgr};
  ASSERT_EQ(RunPrecompile(opts, mgr, diag), 0);
  std::vector<ProtectLicense> kept =
      PrecompiledLibrary::RuntimeLicenses(opts.precompile_output);
  ASSERT_EQ(kept.size(), 1u);
  EXPECT_EQ(kept[0].feature, "simulate");
  EXPECT_EQ(kept[0].match, 7u);
}

}  // namespace
