// §34.5.29.2 runtime_license, Description: the asking before execution.
//
// On meeting the expression in an encrypted model, and before executing it,
// the tool asks the library the value names as §34.5.28.2 has it asked; where
// the answer is not the match value, execution does not begin and the error
// includes the value the entry function returned. The reading records each
// such expression (test_preprocessor_subclause_34_05_29_02.cpp), and the run
// asks them with RuntimeLicensesGranted
// (src/driver/protect_license_libraries.h) before synthesis or simulation.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "driver/protect_license_libraries.h"
#include "helpers_license_library.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

// The run's asking of the runtime licences one model states, each met at a
// line of its own in a recovered text.
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

// Every licence answered with its match value licenses execution, and nothing
// is reported.
TEST(ProtectRuntimeLicenseAsking, MatchingAnswersLetExecutionBegin) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  EXPECT_TRUE(asking.Granted());
  EXPECT_TRUE(asking.diag.Diagnostics().empty());
}

// One answered otherwise does not, so execution does not begin.
TEST(ProtectRuntimeLicenseAsking, AnotherAnswerKeepsExecutionFromBeginning) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  asking.Met("run", 42, 3);
  EXPECT_FALSE(asking.Granted());
}

// And it is reported at the licence's line, with the value returned.
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

// The exit function each licence names is called once the run is over,
// whatever the answers were.
TEST(ProtectRuntimeLicenseAsking, EachLicenceIsReleased) {
  RuntimeAsking asking;
  asking.Met("open", 42, 2);
  asking.Met("run", 42, 3);
  asking.Granted();
  asking.libraries.Release();
  EXPECT_EQ(asking.library.Released(), 2);
}

}  // namespace
