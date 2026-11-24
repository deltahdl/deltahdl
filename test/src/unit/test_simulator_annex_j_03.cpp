#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "helpers_command_line.h"
#include "simulator/foreign_code.h"

using namespace delta;

namespace {

TEST(ForeignCodeLocation, TheRootSwitchIsSvRoot) {
  EXPECT_EQ(ForeignCodeRootSwitch(), "-sv_root");
}

TEST(ForeignCodeLocation, TheRootIsPrependedToRelativePathNames) {
  ForeignCodeLocator locator;
  locator.SetRoot("/ip/vendor");
  EXPECT_TRUE(locator.HasRoot());
  EXPECT_EQ(locator.Root(), "/ip/vendor");
  EXPECT_EQ(locator.Resolve("lib/model"), "/ip/vendor/lib/model");
  EXPECT_EQ(locator.Resolve("/abs/model"), "/abs/model");
}

TEST(ForeignCodeLocation, TheWorkingDirectoryIsTheDefaultUntilARootIsGiven) {
  ForeignCodeLocator locator;
  EXPECT_FALSE(locator.HasRoot());
  const std::string kCwd = locator.Root();
  EXPECT_FALSE(kCwd.empty());
  EXPECT_EQ(locator.Resolve("early.so"), kCwd + "/early.so");
  locator.SetRoot("/ip/vendor");
  EXPECT_EQ(locator.Resolve("late.so"), "/ip/vendor/late.so");
}

TEST(ForeignCodeLocation, ALaterRootReplacesTheEarlier) {
  ForeignCodeLocator locator;
  locator.SetRoot("/first");
  locator.SetRoot("/second");
  EXPECT_EQ(locator.Resolve("x"), "/second/x");
}

TEST(ForeignCodeLocation, TheDriverTakesSvRoot) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-sv_root", "/ip/vendor", "top.sv"}, opts));
  EXPECT_EQ(opts.sv_root, "/ip/vendor");
  CliOptions none;
  EXPECT_TRUE(ParseCommandLine({"top.sv"}, none));
  EXPECT_TRUE(none.sv_root.empty());
}

TEST(ForeignCodeLocation, ARootSwitchWithoutItsDirectoryIsRefused) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(
      ParseCommandLineCapturingStderr({"top.sv", "-sv_root"}, opts, err));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_TRUE(opts.sv_root.empty());
  EXPECT_NE(err.find("-sv_root expects a value"), std::string::npos);
}

TEST(ForeignCodeLocation, ARelativeRootPrefixesTheNamesThatFollowIt) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-sv_root", "vendor/ip", "-sv_lib", "lib/model",
                                "-sv_liblist", "boot", "top.sv"},
                               opts));
  EXPECT_EQ(opts.sv_root, "vendor/ip");
  EXPECT_EQ(opts.sv_libs, std::vector<std::string>{"vendor/ip/lib/model"});
  ASSERT_EQ(opts.sv_liblists.size(), 1u);
  EXPECT_EQ(opts.sv_liblists[0].path, "vendor/ip/boot");
  EXPECT_EQ(opts.sv_liblists[0].root, "vendor/ip");
}

TEST(ForeignCodeLocation, ALaterRelativeRootIsNotTakenUnderTheEarlierRoot) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-sv_root", "/first", "-sv_root", "second",
                                "-sv_lib", "model", "top.sv"},
                               opts));
  EXPECT_EQ(opts.sv_libs, std::vector<std::string>{"second/model"});
}

TEST(ForeignCodeLocation, AnAbsoluteLibraryAfterARootIsLeftUnchanged) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-sv_root", "/nonexistent", "-sv_lib",
                                "/abs/model", "-sv_lib", "model", "top.sv"},
                               opts));
  const std::vector<std::string> kLibs = {"/abs/model", "/nonexistent/model"};
  EXPECT_EQ(opts.sv_libs, kLibs);
}

TEST(ForeignCodeLocation, DISABLED_TheRootSwitchMayRepeat) {
  EXPECT_TRUE(ForeignCodeSwitchMayRepeat("-sv_root"));
}

}  // namespace
