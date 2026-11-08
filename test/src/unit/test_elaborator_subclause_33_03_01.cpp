#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "helpers_command_line.h"

using namespace delta;

namespace {

TEST(LibraryMapCommandLine, MapFileIsNotASourceDescription) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"lib.map", "top.v", "adder.v"}, opts));
  EXPECT_EQ(opts.library_map_files, std::vector<std::string>{"lib.map"});
  EXPECT_EQ(opts.source_files, (std::vector<std::string>{"top.v", "adder.v"}));
}

TEST(LibraryMapCommandLine, SeveralMapFilesKeepTheOrderWritten) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"gates.map", "top.v", "rtl/lib.map"}, opts));
  EXPECT_EQ(opts.library_map_files,
            (std::vector<std::string>{"gates.map", "rtl/lib.map"}));
  EXPECT_EQ(opts.source_files, std::vector<std::string>{"top.v"});
}

TEST(LibraryMapCommandLine, NoMapFileWrittenLeavesTheListEmpty) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"top.v", "adder.vg"}, opts));
  EXPECT_TRUE(opts.library_map_files.empty());
  EXPECT_EQ(opts.source_files, (std::vector<std::string>{"top.v", "adder.vg"}));
}

}  // namespace
