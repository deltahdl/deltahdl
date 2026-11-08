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

TEST(ProtectDecryptLicenseAsking, TheEntryFunctionIsCalledWithTheFeature) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(library.Asking("open", 42));
  EXPECT_TRUE(answer.called) << answer.why_not_called;
  EXPECT_EQ(answer.returned, 42);
}

TEST(ProtectDecryptLicenseAsking, AnotherFeatureIsAnsweredOtherwise) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  ProtectLicenseAnswer answer = libraries.Ask(library.Asking("run", 42));
  EXPECT_EQ(answer.returned, 5);
}

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

TEST(ProtectDecryptLicenseAsking, TheExitFunctionIsCalledOnRelease) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  libraries.Ask(library.Asking("open", 42));
  EXPECT_EQ(library.Released(), 0);
  libraries.Release();
  EXPECT_EQ(library.Released(), 1);
}

TEST(ProtectDecryptLicenseAsking, EachLicenceIsReleasedOnce) {
  LicenseLibrary library;
  {
    ProtectLicenseLibraries libraries;
    libraries.Ask(library.Asking("open", 42));
    libraries.Release();
  }
  EXPECT_EQ(library.Released(), 1);
}

TEST(ProtectDecryptLicenseAsking, TheLibrariesGoingReleaseTheLicence) {
  LicenseLibrary library;
  {
    ProtectLicenseLibraries libraries;
    libraries.Ask(library.Asking("open", 42));
  }
  EXPECT_EQ(library.Released(), 1);
}

TEST(ProtectDecryptLicenseAsking, ARefusedLicenceIsReleasedToo) {
  LicenseLibrary library;
  ProtectLicenseLibraries libraries;
  libraries.Ask(library.Asking("run", 42));
  libraries.Release();
  EXPECT_EQ(library.Released(), 1);
}

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
