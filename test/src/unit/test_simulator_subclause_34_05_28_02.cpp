// §34.5.28.2 decrypt_license, Description: the asking a run supplies.
//
// On meeting the expression in an encrypted model, and before processing the
// decrypted text, the tool loads the library the value names, calls the entry
// function in it with the feature string, and compares the value returned with
// the match value; an exit function, where one is named, is called before the
// tool exits so the licence is released. What the reading does with the
// answer is stated in test_preprocessor_subclause_34_05_28_02.cpp. The cases
// here are the asking itself, ProtectLicenseLibraries
// (src/driver/protect_license_libraries.h), against a library built from C
// for the purpose (helpers_license_library.h).

#include <gtest/gtest.h>

#include <string>

#include "driver/protect_license_libraries.h"
#include "fixture_protect_read.h"
#include "helpers_license_library.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

using namespace delta;

namespace {

// The library is loaded and the entry function called with the feature
// string, the value it returns coming back with the answer.
TEST(ProtectDecryptLicenseAsking, TheEntryFunctionIsCalledWithTheFeature) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(library.Asking("open", 42));
  EXPECT_TRUE(answer.called) << answer.why_not_called;
  EXPECT_EQ(answer.returned, 42);
}

// A different feature is a different question, and the library answers it
// differently: the feature string is what the entry function was passed.
TEST(ProtectDecryptLicenseAsking, AnotherFeatureIsAnsweredOtherwise) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(library.Asking("run", 42));
  EXPECT_EQ(answer.returned, 5);
}

// A library that cannot be loaded leaves the entry function uncalled, and the
// answer carries the loader's account of why, which names the file.
TEST(ProtectDecryptLicenseAsking, ALibraryThatCannotBeLoadedIsNotCalled) {
  LicenseLibrary library;
  ProtectLicense license = library.Asking("open", 42);
  license.library = (library.scratch.dir / "absent.so").string();
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(license);
  EXPECT_FALSE(answer.called);
  EXPECT_NE(answer.why_not_called.find("absent.so"), std::string::npos)
      << answer.why_not_called;
}

// A library defining no function of the entry's name leaves it uncalled too.
TEST(ProtectDecryptLicenseAsking, AnEntryTheLibraryLacksIsNotCalled) {
  LicenseLibrary library;
  ProtectLicense license = library.Asking("open", 42);
  license.entry = "deltahdl_license_absent";
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(license);
  EXPECT_FALSE(answer.called);
  EXPECT_EQ(answer.why_not_called,
            "the library defines no function of that name");
}

// The exit function is called before the tool exits, which is when the run
// releases what it asked, and not before.
TEST(ProtectDecryptLicenseAsking, TheExitFunctionIsCalledOnRelease) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  libraries.Ask(library.Asking("open", 42));
  EXPECT_EQ(library.Released(), 0);
  libraries.Release();
  EXPECT_EQ(library.Released(), 1);
}

// Each licence asked is released once: a release already made is not made
// again when the libraries go.
TEST(ProtectDecryptLicenseAsking, EachLicenceIsReleasedOnce) {
  LicenseLibrary library;
  {
    ProtectLicenseLibraries libraries;
    libraries.Ask(library.Asking("open", 42));
    libraries.Release();
  }
  EXPECT_EQ(library.Released(), 1);
}

// And the libraries going release what was not released yet, which is how a
// run ends.
TEST(ProtectDecryptLicenseAsking, TheLibrariesGoingReleaseTheLicence) {
  LicenseLibrary library;
  {
    ProtectLicenseLibraries libraries;
    libraries.Ask(library.Asking("open", 42));
  }
  EXPECT_EQ(library.Released(), 1);
}

// The exit function is called where the licence was refused as well: either
// way the tool goes on to exit.
TEST(ProtectDecryptLicenseAsking, ARefusedLicenceIsReleasedToo) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  libraries.Ask(library.Asking("run", 42));
  libraries.Release();
  EXPECT_EQ(library.Released(), 1);
}

// The whole of it through a reading: an envelope whose model states a
// decrypt_license naming the library is decrypted where the library's answer
// is the match value.
TEST(ProtectDecryptLicenseAsking, AnEnvelopeLicensedByTheLibraryDecrypts) {
  LicenseLibrary library;
  std::string source = "`pragma protect begin\n";
  source += "`pragma protect decrypt_license=(library=\"" + library.file +
            "\", entry=\"deltahdl_license_check\", feature=\"open\", "
            "match=42)\n";
  source += "module licensed_m; endmodule\n";
  source += "`pragma protect end\n";
  ProtectLicenseLibraries libraries;
  PreprocConfig config = ReadSource::KeyConfig(kReadingExchangeKey);
  config.ask_license = libraries.Asker();
  ReadSource run(EncryptedByTheAuthor(source), config);
  EXPECT_TRUE(Holds(run.text, "module licensed_m;")) << run.text;
}

}  // namespace
