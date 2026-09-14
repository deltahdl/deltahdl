#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "simulator/foreign_code.h"

using namespace delta;

namespace {

// §J.3: the path names of the annex are location independent through the
// switch -sv_root, which takes a single directory path name.
TEST(ForeignCodeLocation, TheRootSwitchIsSvRoot) {
  EXPECT_EQ(ForeignCodeRootSwitch(), "-sv_root");
}

// §J.3: the directory -sv_root gives is prepended to any relative path name
// specified, and an absolute path name is left as it is.
TEST(ForeignCodeLocation, TheRootIsPrependedToRelativePathNames) {
  ForeignCodeLocator locator;
  locator.SetRoot("/ip/vendor");
  EXPECT_TRUE(locator.HasRoot());
  EXPECT_EQ(locator.Root(), "/ip/vendor");
  EXPECT_EQ(locator.Resolve("lib/model"), "/ip/vendor/lib/model");
  EXPECT_EQ(locator.Resolve("/abs/model"), "/abs/model");
}

// §J.3: in the absence of the switch the user's current working directory
// is the default root, and a relative name processed before any -sv_root
// resolves against it while one processed after resolves against the root
// -- each name resolved as it is processed.
TEST(ForeignCodeLocation, TheWorkingDirectoryIsTheDefaultUntilARootIsGiven) {
  ForeignCodeLocator locator;
  EXPECT_FALSE(locator.HasRoot());
  const std::string kCwd = locator.Root();
  EXPECT_FALSE(kCwd.empty());
  EXPECT_EQ(locator.Resolve("early.so"), kCwd + "/early.so");
  locator.SetRoot("/ip/vendor");
  EXPECT_EQ(locator.Resolve("late.so"), "/ip/vendor/late.so");
}

// §J.3: a later -sv_root replaces the earlier root rather than stacking on
// it, the switch receiving a single directory.
TEST(ForeignCodeLocation, ALaterRootReplacesTheEarlier) {
  ForeignCodeLocator locator;
  locator.SetRoot("/first");
  locator.SetRoot("/second");
  EXPECT_EQ(locator.Resolve("x"), "/second/x");
}

// Runs ParseArgs over the words as written on a command line, the program
// name prepended as argv[0].
bool ParseCommandLine(const std::vector<std::string>& args, CliOptions& opts) {
  std::vector<std::string> words;
  words.emplace_back("deltahdl");
  for (const std::string& arg : args) words.push_back(arg);
  std::vector<char*> argv;
  argv.reserve(words.size());
  for (std::string& word : words) argv.push_back(word.data());
  return ParseArgs(static_cast<int>(argv.size()), argv.data(), opts);
}

// §J.3: the driver takes -sv_root with its directory, and leaves the root
// empty -- the working directory's stand-in -- where the switch is absent.
TEST(ForeignCodeLocation, TheDriverTakesSvRoot) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-sv_root", "/ip/vendor", "top.sv"}, opts));
  EXPECT_EQ(opts.sv_root, "/ip/vendor");
  CliOptions none;
  EXPECT_TRUE(ParseCommandLine({"top.sv"}, none));
  EXPECT_TRUE(none.sv_root.empty());
}

}  // namespace
