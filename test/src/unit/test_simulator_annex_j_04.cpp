#include <gtest/gtest.h>
#include <stdlib.h>
#include <unistd.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "helpers_command_line.h"
#include "helpers_reported_error.h"
#include "simulator/foreign_code.h"
#include "simulator/shared_library.h"

using namespace delta;

namespace fs = std::filesystem;

namespace {

// §J.4: compiled object code is specified by an entry in a bootstrap file,
// whose location -sv_liblist gives, or by -sv_lib naming the file without
// its extension; either switch can be used multiple times.
TEST(ForeignCodeObjectInclusion, EachMethodHasItsSwitchAndEitherMayRepeat) {
  EXPECT_EQ(ForeignCodeLibListSwitch(), "-sv_liblist");
  EXPECT_EQ(ForeignCodeLibSwitch(), "-sv_lib");
  EXPECT_EQ(
      ForeignCodeSwitchOf(ForeignCodeSpecificationMethod::kBootstrapFileEntry),
      "-sv_liblist");
  EXPECT_EQ(ForeignCodeSwitchOf(ForeignCodeSpecificationMethod::kLibSwitch),
            "-sv_lib");
  EXPECT_TRUE(ForeignCodeSwitchMayRepeat("-sv_liblist"));
  EXPECT_TRUE(ForeignCodeSwitchMayRepeat("-sv_lib"));
  EXPECT_FALSE(ForeignCodeSwitchMayRepeat("-sv_root"));
}

// §J.4: both methods shall be provided and made available concurrently, any
// mixture of their usage permitted.
TEST(ForeignCodeObjectInclusion, BothMethodsAreConcurrentAndMayBeMixed) {
  EXPECT_TRUE(ForeignCodeMethodsAreAvailableConcurrently());
  EXPECT_TRUE(ForeignCodeMethodsMayBeMixed());
}

// §J.4: the object code is a shared library with the platform's extension,
// which the application identifies and appends to the path name -sv_lib or
// a bootstrap entry gives without it.
TEST(ForeignCodeObjectInclusion, TheApplicationAppendsThePlatformExtension) {
  const std::string kExtension(ForeignCodeSharedLibraryExtension());
  ASSERT_FALSE(kExtension.empty());
  EXPECT_EQ(kExtension.front(), '.');
#if defined(__linux__)
  EXPECT_EQ(kExtension, ".so");
#endif
  EXPECT_EQ(ForeignCodeSharedLibraryFileName("myclibs/lib1"),
            "myclibs/lib1" + kExtension);
  EXPECT_EQ(ForeignCodeResponsibleFor(ForeignCodeDuty::kIdentifyTheExtension),
            ForeignCodeParty::kApplication);
  EXPECT_EQ(ForeignCodeResponsibleFor(ForeignCodeDuty::kAppendTheExtension),
            ForeignCodeParty::kApplication);
}

// §J.4: the provider of the compiled code resolves its external references,
// avoids interference with other software and selects the software version;
// the application need only load the object code SystemVerilog code or
// registration functions reference.
TEST(ForeignCodeObjectInclusion, TheProviderAnswersForTheObjectsContents) {
  EXPECT_EQ(
      ForeignCodeResponsibleFor(ForeignCodeDuty::kResolveExternalReferences),
      ForeignCodeParty::kProvider);
  EXPECT_EQ(ForeignCodeResponsibleFor(
                ForeignCodeDuty::kAvoidInterferenceWithOtherSoftware),
            ForeignCodeParty::kProvider);
  EXPECT_EQ(
      ForeignCodeResponsibleFor(ForeignCodeDuty::kSelectTheSoftwareVersion),
      ForeignCodeParty::kProvider);
  EXPECT_EQ(ForeignCodeLoadRequired(),
            ForeignCodeLoadScope::kReferencedObjectCodeOnly);
}

// §J.4: all compiled object code is loaded in specification order -- the
// bootstrap file's content from its first line, then the -sv_lib switches in
// order of occurrence.
TEST(ForeignCodeObjectInclusion, TheBootstrapFileLoadsBeforeTheSwitches) {
  const std::vector<ForeignCodeLibrary> kOrder = ForeignCodeLoadOrder(
      {"/home/user/myclibs/lib1", "/home/user/myclibs/lib3"},
      {"/home/user/proj1/clibs/lib4", "/home/user/proj3/clibs/lib2"});
  ASSERT_EQ(kOrder.size(), 4u);
  EXPECT_EQ(kOrder[0].path, "/home/user/myclibs/lib1");
  EXPECT_EQ(kOrder[0].method,
            ForeignCodeSpecificationMethod::kBootstrapFileEntry);
  EXPECT_EQ(kOrder[1].path, "/home/user/myclibs/lib3");
  EXPECT_EQ(kOrder[2].path, "/home/user/proj1/clibs/lib4");
  EXPECT_EQ(kOrder[2].method, ForeignCodeSpecificationMethod::kLibSwitch);
  EXPECT_EQ(kOrder[3].path, "/home/user/proj3/clibs/lib2");
}

// §J.4: any library is loaded only once, and among multiple occurrences of
// the same file the specification order gives the precedence: a file the
// bootstrap file located overrides the same file -sv_lib specified, and of
// two -sv_lib occurrences the first is the one that loads.
TEST(ForeignCodeObjectInclusion, ALibraryLoadsOnceAndTheBootstrapEntryWins) {
  const std::vector<ForeignCodeLibrary> kOrder =
      ForeignCodeLoadOrder({"/ip/a"}, {"/ip/b", "/ip/a", "/ip/b", "/ip/c"});
  ASSERT_EQ(kOrder.size(), 3u);
  EXPECT_EQ(kOrder[0].path, "/ip/a");
  EXPECT_EQ(kOrder[0].method,
            ForeignCodeSpecificationMethod::kBootstrapFileEntry);
  EXPECT_EQ(kOrder[1].path, "/ip/b");
  EXPECT_EQ(kOrder[1].method, ForeignCodeSpecificationMethod::kLibSwitch);
  EXPECT_EQ(kOrder[2].path, "/ip/c");
}

// A directory of shared library files for the identity of §J.4 to be read
// off the filesystem, removed when the test ends.
struct ForeignCodeLibraryDir {
  fs::path dir;

  ForeignCodeLibraryDir() {
    dir = fs::temp_directory_path() /
          ("delta_annex_j_04_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~ForeignCodeLibraryDir() { fs::remove_all(dir); }

  // The path name without extension of a library written under `name`.
  std::string Library(const std::string& name) const {
    const fs::path kWithout = dir / name;
    const std::ofstream kFile(
        ForeignCodeSharedLibraryFileName(kWithout.string()));
    return kWithout.string();
  }

  // The path name without extension of a shared library the system C
  // compiler built from `c_source` under `name`.
  std::string Built(const std::string& name,
                    const std::string& c_source) const {
    const fs::path kWithout = dir / name;
    const std::string kError =
        BuildCSharedLibrary(c_source, kWithout.string(), "cc");
    EXPECT_EQ(kError, "");
    return kWithout.string();
  }

  // The path name without extension of a link to the library `target`.
  std::string Link(const std::string& name, const std::string& target) const {
    const fs::path kWithout = dir / name;
    fs::create_symlink(ForeignCodeSharedLibraryFileName(target),
                       ForeignCodeSharedLibraryFileName(kWithout.string()));
    return kWithout.string();
  }
};

// §J.4: files having the same path name, or that can be identified as being
// identical -- by comparing inodes where links refer to one file -- are
// occurrences of the same file; files that are neither are not.
TEST(ForeignCodeObjectInclusion, TheSameFileIsKnownByPathNameOrByInode) {
  EXPECT_TRUE(ForeignCodeIsSameFile("/ip/a", "/ip/a"));
  EXPECT_TRUE(ForeignCodeIsSameFile("/ip/x/../a", "/ip/a"));
  EXPECT_FALSE(ForeignCodeIsSameFile("/ip/a", "/ip/b"));
  const ForeignCodeLibraryDir kLibs;
  const std::string kLib = kLibs.Library("lib1");
  const std::string kLink = kLibs.Link("alias", kLib);
  const std::string kOther = kLibs.Library("lib2");
  EXPECT_TRUE(ForeignCodeIsSameFile(kLib, kLink));
  EXPECT_FALSE(ForeignCodeIsSameFile(kLib, kOther));
  const std::vector<ForeignCodeLibrary> kOrder =
      ForeignCodeLoadOrder({kLib}, {kLink, kOther});
  ASSERT_EQ(kOrder.size(), 2u);
  EXPECT_EQ(kOrder[0].path, kLib);
  EXPECT_EQ(kOrder[1].path, kOther);
}

// §J.4 with §J.3: the driver takes -sv_lib and -sv_liblist, each any number
// of times in order, each value resolved as it is processed -- a relative
// name before -sv_root against the working directory, one after against the
// root, and an absolute name as it is.
TEST(ForeignCodeObjectInclusion, TheDriverTakesSvLibAndSvLiblistAsProcessed) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(
      {"-sv_lib", "early/lib", "-sv_root", "/ip", "-sv_lib", "late/lib",
       "-sv_liblist", "/abs/boot.txt", "-sv_liblist", "proj/boot", "top.sv"},
      opts));
  const std::string kCwd = ForeignCodeLocator().Root();
  ASSERT_EQ(opts.sv_libs.size(), 2u);
  EXPECT_EQ(opts.sv_libs[0], kCwd + "/early/lib");
  EXPECT_EQ(opts.sv_libs[1], "/ip/late/lib");
  ASSERT_EQ(opts.sv_liblists.size(), 2u);
  EXPECT_EQ(opts.sv_liblists[0].path, "/abs/boot.txt");
  EXPECT_EQ(opts.sv_liblists[1].path, "/ip/proj/boot");
  EXPECT_EQ(opts.source_files, std::vector<std::string>{"top.sv"});
}

// A switch written last with its value left off is the switch with a missing
// value rather than an unknown option, and the parse is refused.
TEST(ForeignCodeObjectInclusion, ASwitchWithoutItsValueIsRefused) {
  CliOptions lib;
  EXPECT_FALSE(ParseCommandLine({"top.sv", "-sv_lib"}, lib));
  EXPECT_TRUE(lib.rejected_argument);
  EXPECT_TRUE(lib.sv_libs.empty());
  CliOptions list;
  EXPECT_FALSE(ParseCommandLine({"top.sv", "-sv_liblist"}, list));
  EXPECT_TRUE(list.rejected_argument);
  EXPECT_TRUE(list.sv_liblists.empty());
}

// A library whose constructor appends `letter` to DELTAHDL_ANNEX_J_04_ORDER
// when the library is loaded, and which defines `symbol`, returning 7.
std::string OrderRecordingLibrary(const std::string& letter,
                                  const std::string& symbol) {
  return "#include <stdio.h>\n"
         "#include <stdlib.h>\n"
         "__attribute__((constructor)) static void loaded(void) {\n"
         "  const char* seen = getenv(\"DELTAHDL_ANNEX_J_04_ORDER\");\n"
         "  char next[64];\n"
         "  snprintf(next, sizeof next, \"%s" +
         letter +
         "\", seen ? seen : \"\");\n"
         "  setenv(\"DELTAHDL_ANNEX_J_04_ORDER\", next, 1);\n"
         "}\n"
         "int " +
         symbol + "(void) { return 7; }\n";
}

// §J.2 and §J.4: the object code a specification names is loaded into the
// simulator, the bootstrap file's entries ahead of the -sv_lib values, and
// what a library defines is a global symbol from then on.
TEST(ForeignCodeObjectLoading, EachLibraryIsLoadedInTheOrderJ4Gives) {
  const ForeignCodeLibraryDir kDir;
  const std::string kSwitch = kDir.Built(
      "switch_lib", OrderRecordingLibrary("s", "deltahdl_annex_j_04_switch"));
  const std::string kEntry = kDir.Built(
      "entry_lib", OrderRecordingLibrary("e", "deltahdl_annex_j_04_entry"));
  setenv("DELTAHDL_ANNEX_J_04_ORDER", "", 1);
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_TRUE(ForeignCodeLoadLibraries({kEntry}, {kSwitch}, diag));
  EXPECT_TRUE(diag.Diagnostics().empty());
  EXPECT_EQ(std::string(std::getenv("DELTAHDL_ANNEX_J_04_ORDER")), "es");
  EXPECT_NE(GlobalSymbol("deltahdl_annex_j_04_switch"), nullptr);
  EXPECT_NE(GlobalSymbol("deltahdl_annex_j_04_entry"), nullptr);
}

// §J.4: a location naming no file once the platform's extension is appended
// is a failure of the run, reported against the location as written.
TEST(ForeignCodeObjectLoading, ALocationWithNoFileIsReported) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({}, {"/no/such/annex_j_04_lib"}, diag));
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "object code file '/no/such/annex_j_04_lib', "
                            "named by -sv_lib, is not there",
                            0, "J.4"));
}

// §J.4: a file that is there but is no shared library the loader can load is
// reported with the loader's own account, and the libraries after it in the
// order are loaded all the same.
TEST(ForeignCodeObjectLoading, AFileTheLoaderRejectsIsReportedWithItsAccount) {
  const ForeignCodeLibraryDir kDir;
  const std::string kEmpty = kDir.Library("not_object_code");
  const std::string kAfter = kDir.Built(
      "after_lib", OrderRecordingLibrary("a", "deltahdl_annex_j_04_after"));
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({kEmpty}, {kAfter}, diag));
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "', named by a bootstrap entry, could not be "
                            "loaded: ",
                            0, "J.4"));
  ASSERT_EQ(diag.Diagnostics().size(), 1U);
  EXPECT_NE(diag.Diagnostics()[0].message.find("not_object_code"),
            std::string::npos);
  EXPECT_NE(GlobalSymbol("deltahdl_annex_j_04_after"), nullptr);
}

}  // namespace
