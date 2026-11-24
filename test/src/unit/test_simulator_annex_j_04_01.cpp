#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

TEST(ForeignCodeBootstrapFile, TheFigureFileListsItsFourLibrariesInOrder) {
  EXPECT_EQ(ForeignCodeBootstrapHeader(), "#!SV_LIBRARIES");
  const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n"
      " myclibs/lib1\n"
      " myclibs/lib3\n"
      " proj1/clibs/lib4\n"
      " proj3/clibs/lib2\n");
  ASSERT_TRUE(kFile.Ok()) << kFile.error;
  ASSERT_EQ(kFile.libraries.size(), 4u);
  EXPECT_EQ(kFile.libraries[0], "myclibs/lib1");
  EXPECT_EQ(kFile.libraries[1], "myclibs/lib3");
  EXPECT_EQ(kFile.libraries[2], "proj1/clibs/lib4");
  EXPECT_EQ(kFile.libraries[3], "proj3/clibs/lib2");
}

TEST(ForeignCodeBootstrapFile, BlanksSurroundEntriesAndCommentsAreSkipped) {
  const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n"
      "# the vendor's models\n"
      "\t  vendor/model   \n"
      "   # and the project's\n"
      " proj/lib\n");
  ASSERT_TRUE(kFile.Ok()) << kFile.error;
  ASSERT_EQ(kFile.libraries.size(), 2u);
  EXPECT_EQ(kFile.libraries[0], "vendor/model");
  EXPECT_EQ(kFile.libraries[1], "proj/lib");
}

TEST(ForeignCodeBootstrapFile, TheFirstLineMustCarryTheHeader) {
  const std::string kMissing =
      "line 1: the first line of a bootstrap file contains #!SV_LIBRARIES";
  EXPECT_EQ(ParseForeignCodeBootstrap(" myclibs/lib1\n").error, kMissing);
  EXPECT_EQ(ParseForeignCodeBootstrap("").error, kMissing);
  EXPECT_TRUE(ParseForeignCodeBootstrap("#!SV_LIBRARIES\n").Ok());
  EXPECT_TRUE(ParseForeignCodeBootstrap("#!SV_LIBRARIES").Ok());
}

TEST(ForeignCodeBootstrapFile, AnEntryIsOnePathPrecededByABlank) {
  const ForeignCodeBootstrap kUnpreceded =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\nmyclibs/lib1\n");
  EXPECT_EQ(kUnpreceded.error,
            "line 2: a library entry has to be indented by one or more blanks");
  const ForeignCodeBootstrap kTwo =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib1 lib2\n");
  EXPECT_EQ(kTwo.error,
            "line 2: a line holds exactly one library entry, and this holds "
            "more");
  const ForeignCodeBootstrap kBlank =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n   \n lib1\n");
  EXPECT_EQ(kBlank.error,
            "line 2: a line holds one library entry or a comment, and this "
            "holds neither");
}

TEST(ForeignCodeBootstrapFile, AnEntryIsKeptAsThePathNameWithoutExtension) {
  const ForeignCodeBootstrap kFile =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n /abs/dir/lib\n rel/lib\n");
  ASSERT_TRUE(kFile.Ok()) << kFile.error;
  EXPECT_EQ(kFile.libraries[0], "/abs/dir/lib");
  ForeignCodeLocator locator;
  locator.SetRoot("/home/user");
  EXPECT_EQ(locator.Resolve(kFile.libraries[1]), "/home/user/rel/lib");
}

TEST(ForeignCodeBootstrapFile, BlanksMaySurroundTheHeaderOnTheFirstLine) {
  for (const char* text :
       {"  #!SV_LIBRARIES\n lib1\n", "#!SV_LIBRARIES  \n lib1\n",
        "\t#!SV_LIBRARIES\t\n lib1\n"}) {
    const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(text);
    EXPECT_TRUE(kFile.Ok()) << kFile.error;
    EXPECT_EQ(kFile.libraries, std::vector<std::string>{"lib1"}) << text;
  }
}

TEST(ForeignCodeBootstrapFile, AHeaderOtherThanTheStringIsRefused) {
  const std::string kMissing =
      "line 1: the first line of a bootstrap file contains #!SV_LIBRARIES";
  for (const char* text :
       {"#! SV_LIBRARIES\n lib1\n", "#!sv_libraries\n lib1\n",
        "\n#!SV_LIBRARIES\n lib1\n", "# note\n#!SV_LIBRARIES\n lib1\n"}) {
    EXPECT_EQ(ParseForeignCodeBootstrap(text).error, kMissing) << text;
  }
}

TEST(ForeignCodeBootstrapFile, ACommentSharesNoLineWithAnEntry) {
  EXPECT_EQ(ParseForeignCodeBootstrap("#!SV_LIBRARIES\n a # c\n").error,
            "line 2: a line holds exactly one library entry, and this holds "
            "more");
  const ForeignCodeBootstrap kOwnLine =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n a\n # c\n");
  ASSERT_TRUE(kOwnLine.Ok()) << kOwnLine.error;
  EXPECT_EQ(kOwnLine.libraries, std::vector<std::string>{"a"});
}

TEST(ForeignCodeBootstrapFile, AnEmptyLineIsNoEntry) {
  EXPECT_EQ(ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib1\n\n lib2\n").error,
            "line 3: a library entry has to be indented by one or more blanks");
  const ForeignCodeBootstrap kWithout =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib1\n lib2\n");
  EXPECT_TRUE(kWithout.Ok()) << kWithout.error;
  EXPECT_EQ(kWithout.libraries.size(), 2u);
}

}  // namespace
