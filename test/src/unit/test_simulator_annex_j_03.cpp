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

}  // namespace
