#include <gtest/gtest.h>
#include <unistd.h>

#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"
#include "helpers_reported_error.h"
#include "simulator/dpi_binding.h"
#include "simulator/foreign_code.h"
#include "simulator/lowerer.h"
#include "simulator/shared_library.h"

using namespace delta;

namespace fs = std::filesystem;

namespace {

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
}

TEST(ForeignCodeObjectInclusion, BothMethodsAreConcurrentAndMayBeMixed) {
  EXPECT_TRUE(ForeignCodeMethodsAreAvailableConcurrently());
  EXPECT_TRUE(ForeignCodeMethodsMayBeMixed());
}

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

struct ForeignCodeLibraryDir {
  fs::path dir;

  ForeignCodeLibraryDir() {
    dir = fs::temp_directory_path() /
          ("delta_annex_j_04_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~ForeignCodeLibraryDir() { fs::remove_all(dir); }

  std::string Library(const std::string& name) const {
    const fs::path kWithout = dir / name;
    const std::ofstream kFile(
        ForeignCodeSharedLibraryFileName(kWithout.string()));
    return kWithout.string();
  }

  std::string Built(const std::string& name,
                    const std::string& c_source) const {
    const fs::path kWithout = dir / name;
    const std::string kError =
        BuildCSharedLibrary(c_source, kWithout.string(), "cc");
    EXPECT_EQ(kError, "");
    return kWithout.string();
  }

  std::string Link(const std::string& name, const std::string& target) const {
    const fs::path kWithout = dir / name;
    fs::create_symlink(ForeignCodeSharedLibraryFileName(target),
                       ForeignCodeSharedLibraryFileName(kWithout.string()));
    return kWithout.string();
  }
};

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

std::string OrderVariable() {
  return std::string("DELTAHDL_ORDER_") +
         ::testing::UnitTest::GetInstance()->current_test_info()->name();
}

std::string RecordedOrder() {
  const char* order = std::getenv(OrderVariable().c_str());
  return order == nullptr ? "" : order;
}

std::string OrderRecordingLibrary(const std::string& letter,
                                  const std::string& symbol) {
  return "#include <stdio.h>\n"
         "#include <stdlib.h>\n"
         "__attribute__((constructor)) static void loaded(void) {\n"
         "  const char* seen = getenv(\"" +
         OrderVariable() +
         "\");\n"
         "  char next[64];\n"
         "  snprintf(next, sizeof next, \"%s" +
         letter +
         "\", seen ? seen : \"\");\n"
         "  setenv(\"" +
         OrderVariable() +
         "\", next, 1);\n"
         "}\n"
         "int " +
         symbol + "(void) { return 7; }\n";
}

TEST(ForeignCodeObjectLoading, EachLibraryIsLoadedInTheOrderJ4Gives) {
  const ForeignCodeLibraryDir kDir;
  const std::string kSwitch = kDir.Built(
      "switch_lib", OrderRecordingLibrary("s", "deltahdl_annex_j_04_switch"));
  const std::string kEntry = kDir.Built(
      "entry_lib", OrderRecordingLibrary("e", "deltahdl_annex_j_04_entry"));
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_TRUE(ForeignCodeLoadLibraries({kEntry}, {kSwitch}, diag));
  EXPECT_TRUE(diag.Diagnostics().empty());
  EXPECT_EQ(RecordedOrder(), "es");
  EXPECT_NE(GlobalSymbol("deltahdl_annex_j_04_switch"), nullptr);
  EXPECT_NE(GlobalSymbol("deltahdl_annex_j_04_entry"), nullptr);
}

TEST(ForeignCodeObjectLoading, ALocationWithNoFileIsReported) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({}, {"/no/such/annex_j_04_lib"}, diag));
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "object code file '/no/such/annex_j_04_lib', "
                            "named by -sv_lib, is not there",
                            0, "J.4"));
}

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

TEST(ForeignCodeObjectInclusion,
     AFileRepeatedInABootstrapFileKeepsItsFirstEntry) {
  const ForeignCodeLibraryDir kLibs;
  const std::string kLib = kLibs.Library("twice");
  kLibs.Link("twice_alias", kLib);
  const std::string kOther = kLibs.Library("between");
  const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n twice\n between\n twice\n twice_alias\n");
  ASSERT_TRUE(kFile.Ok()) << kFile.error;
  const std::vector<ForeignCodeLibrary> kOrder = ForeignCodeLoadOrder(
      ForeignCodeResolveBootstrapEntries(kFile, kLibs.dir.string()), {});
  ASSERT_EQ(kOrder.size(), 2u);
  EXPECT_EQ(kOrder[0].path, kLib);
  EXPECT_EQ(kOrder[0].method,
            ForeignCodeSpecificationMethod::kBootstrapFileEntry);
  EXPECT_EQ(kOrder[1].path, kOther);
}

TEST(ForeignCodeObjectInclusion, AFileInTwoBootstrapFilesKeepsTheFirstsEntry) {
  const ForeignCodeBootstrap kFirst =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n a\n b\n");
  const ForeignCodeBootstrap kSecond =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n c\n b\n a\n");
  std::vector<std::string> entries =
      ForeignCodeResolveBootstrapEntries(kFirst, "/ip");
  for (const std::string& entry :
       ForeignCodeResolveBootstrapEntries(kSecond, "/ip")) {
    entries.push_back(entry);
  }
  const std::vector<std::string> kFiles = {
      ForeignCodeSharedLibraryFileName("/ip/a"),
      ForeignCodeSharedLibraryFileName("/ip/b"),
      ForeignCodeSharedLibraryFileName("/ip/c")};
  EXPECT_EQ(ForeignCodeLibraryFileNames(ForeignCodeLoadOrder(entries, {})),
            kFiles);
}

TEST(ForeignCodeObjectLoading, ALibraryNamedSeveralTimesIsInitializedOnce) {
  const ForeignCodeLibraryDir kDir;
  const std::string kLib = kDir.Built(
      "repeated", OrderRecordingLibrary("r", "deltahdl_annex_j_04_repeated"));
  const std::string kLink = kDir.Link("repeated_alias", kLib);
  const std::string kLast = kDir.Built(
      "last", OrderRecordingLibrary("l", "deltahdl_annex_j_04_last"));
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_TRUE(ForeignCodeLoadLibraries({kLib, kLib, kLink},
                                       {kLast, kLib, kLink, kLast}, diag));
  EXPECT_TRUE(diag.Diagnostics().empty());
  EXPECT_EQ(RecordedOrder(), "rl");
}

TEST(ForeignCodeObjectLoading, ANameWrittenWithItsExtensionIsReported) {
  const ForeignCodeLibraryDir kDir;
  const std::string kLib = kDir.Built(
      "extended", OrderRecordingLibrary("x", "deltahdl_annex_j_04_extended"));
  const std::string kWithExtension = ForeignCodeSharedLibraryFileName(kLib);
  ASSERT_TRUE(fs::exists(kWithExtension));
  SourceManager mgr;
  DiagEngine with(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({}, {kWithExtension}, with));
  EXPECT_TRUE(ReportedError(
      with.Diagnostics(),
      "object code file '" + kWithExtension +
          "', named by -sv_lib, is not there with the platform's shared "
          "library extension appended",
      0, "J.4"));
  DiagEngine entry(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({kWithExtension}, {}, entry));
  EXPECT_TRUE(ReportedError(entry.Diagnostics(),
                            "', named by a bootstrap entry, is not there", 0,
                            "J.4"));
  DiagEngine without(mgr);
  EXPECT_TRUE(ForeignCodeLoadLibraries({}, {kLib}, without));
  EXPECT_TRUE(without.Diagnostics().empty());
}

TEST(ForeignCodeObjectLoading, AFileWithAnotherExtensionIsNotTheLibrary) {
  const ForeignCodeLibraryDir kDir;
  const std::string kLib = kDir.Built(
      "archived", OrderRecordingLibrary("v", "deltahdl_annex_j_04_archived"));
  fs::rename(ForeignCodeSharedLibraryFileName(kLib), kLib + ".a");
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_FALSE(ForeignCodeLoadLibraries({}, {kLib}, diag));
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(),
      "object code file '" + kLib + "', named by -sv_lib, is not there", 0,
      "J.4"));
}

uint64_t ResultOfAnImportedCall(const std::string& c_name) {
  SimFixture f;
  auto* design = ElaborateSrc("module t;\n  import \"DPI-C\" " + c_name +
                                  " = function int imported(input int a);\n"
                                  "  int r;\n"
                                  "  initial r = imported(7);\n"
                                  "endmodule\n",
                              f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  BindDesignDpiImports(f.ctx);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* r = f.ctx.FindVariable("r");
  EXPECT_NE(r, nullptr);
  return r == nullptr ? 0 : r->value.ToUint64();
}

TEST(ForeignCodeObjectLoading, AnImportReachesAFunctionOfEitherMethodsLibrary) {
  const ForeignCodeLibraryDir kDir;
  const std::string kEntry = kDir.Built(
      "triple", "int deltahdl_annex_j_04_triple(int a) { return 3 * a; }\n");
  const std::string kSwitch = kDir.Built(
      "square", "int deltahdl_annex_j_04_square(int a) { return a * a; }\n");
  SourceManager mgr;
  DiagEngine diag(mgr);
  ASSERT_TRUE(ForeignCodeLoadLibraries({kEntry}, {kSwitch}, diag));
  EXPECT_EQ(ResultOfAnImportedCall("deltahdl_annex_j_04_triple"), 21U);
  EXPECT_EQ(ResultOfAnImportedCall("deltahdl_annex_j_04_square"), 49U);
}

TEST(ForeignCodeObjectLoading, AnImportReachesObjectCodeCompiledFromCxx) {
  const ForeignCodeLibraryDir kDir;
  const std::string kLib = (kDir.dir / "from_cxx").string();
  ASSERT_EQ(BuildCSharedLibrary(
                "namespace {\n"
                "struct Offset {\n"
                "  int value;\n"
                "  Offset() : value(100) {}\n"
                "} offset;\n"
                "template <typename T> T Add(T a, T b) { return a + b; }\n"
                "}\n"
                "extern \"C\" int deltahdl_annex_j_04_from_cxx(int a) {\n"
                "  return Add(a, offset.value);\n"
                "}\n",
                kLib, "c++"),
            "");
  SourceManager mgr;
  DiagEngine diag(mgr);
  ASSERT_TRUE(ForeignCodeLoadLibraries({}, {kLib}, diag));
  EXPECT_EQ(ResultOfAnImportedCall("deltahdl_annex_j_04_from_cxx"), 107U);
}

}  // namespace
