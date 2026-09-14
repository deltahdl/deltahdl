#include <gtest/gtest.h>

#include <string>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

// §J.4.1: the bootstrap file of Figure J.2 -- the header line and four
// entries, each the path name without extension of an object code file,
// preceded by a blank -- lists the four libraries in order.
TEST(ForeignCodeBootstrapFile, TheFigureFileListsItsFourLibrariesInOrder) {
  EXPECT_EQ(ForeignCodeBootstrapHeader(), "#!SV_LIBRARIES");
  const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n"
      " myclibs/lib1\n"
      " myclibs/lib3\n"
      " proj1/clibs/lib4\n"
      " proj3/clibs/lib2\n");
  ASSERT_TRUE(kFile.ok()) << kFile.error;
  ASSERT_EQ(kFile.libraries.size(), 4u);
  EXPECT_EQ(kFile.libraries[0], "myclibs/lib1");
  EXPECT_EQ(kFile.libraries[1], "myclibs/lib3");
  EXPECT_EQ(kFile.libraries[2], "proj1/clibs/lib4");
  EXPECT_EQ(kFile.libraries[3], "proj3/clibs/lib2");
}

// §J.4.1 b) and c): an entry may be surrounded by any number of blanks, and
// comment lines -- # after any number of blanks -- may stand between the
// entries without becoming entries themselves.
TEST(ForeignCodeBootstrapFile, BlanksSurroundEntriesAndCommentsAreSkipped) {
  const ForeignCodeBootstrap kFile = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n"
      "# the vendor's models\n"
      "\t  vendor/model   \n"
      "   # and the project's\n"
      " proj/lib\n");
  ASSERT_TRUE(kFile.ok()) << kFile.error;
  ASSERT_EQ(kFile.libraries.size(), 2u);
  EXPECT_EQ(kFile.libraries[0], "vendor/model");
  EXPECT_EQ(kFile.libraries[1], "proj/lib");
}

// §J.4.1 a): the first line contains the header string, and a file whose
// first line does not is no bootstrap file -- an empty file among them.
TEST(ForeignCodeBootstrapFile, TheFirstLineMustCarryTheHeader) {
  EXPECT_FALSE(ParseForeignCodeBootstrap(" myclibs/lib1\n").ok());
  EXPECT_FALSE(ParseForeignCodeBootstrap("").ok());
  EXPECT_TRUE(ParseForeignCodeBootstrap("#!SV_LIBRARIES\n").ok());
  EXPECT_TRUE(ParseForeignCodeBootstrap("#!SV_LIBRARIES").ok());
}

// §J.4.1 b): at least one blank precedes an entry, a line holds exactly one
// entry, and a line of blanks alone is neither an entry nor a comment.
TEST(ForeignCodeBootstrapFile, AnEntryIsOnePathPrecededByABlank) {
  const ForeignCodeBootstrap kUnpreceded =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\nmyclibs/lib1\n");
  EXPECT_FALSE(kUnpreceded.ok());
  EXPECT_NE(kUnpreceded.error.find("line 2"), std::string::npos);
  const ForeignCodeBootstrap kTwo =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib1 lib2\n");
  EXPECT_FALSE(kTwo.ok());
  EXPECT_NE(kTwo.error.find("exactly one"), std::string::npos);
  const ForeignCodeBootstrap kBlank =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n   \n lib1\n");
  EXPECT_FALSE(kBlank.ok());
  EXPECT_NE(kBlank.error.find("line 2"), std::string::npos);
}

// §J.4.1 b): an entry is the path name without extension, equivalent to the
// value of -sv_lib, kept as written for the application to extend and to
// resolve against the root of §J.3.
TEST(ForeignCodeBootstrapFile, AnEntryIsKeptAsThePathNameWithoutExtension) {
  const ForeignCodeBootstrap kFile =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n /abs/dir/lib\n rel/lib\n");
  ASSERT_TRUE(kFile.ok()) << kFile.error;
  EXPECT_EQ(kFile.libraries[0], "/abs/dir/lib");
  ForeignCodeLocator locator;
  locator.SetRoot("/home/user");
  EXPECT_EQ(locator.Resolve(kFile.libraries[1]), "/home/user/rel/lib");
}

}  // namespace
