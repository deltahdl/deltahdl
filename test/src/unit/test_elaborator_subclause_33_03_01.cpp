// §33.3.1 Specifying libraries -- the library map file: the command line's
// half of the mechanism.
//
// Each tool chooses the file's name and how it is read, but every compliant
// tool lets an invocation name one or more library map files, and several are
// read in the order they were named. In this tool a command-line word ending in
// .map names one, and every case here calls ParseArgs (driver/cli_options.h)
// and reads where such a word went. What the map then does to the design is
// covered by the library_map_* cases in test/src/e2e, which run the whole
// program over a map and the source files it maps.

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
