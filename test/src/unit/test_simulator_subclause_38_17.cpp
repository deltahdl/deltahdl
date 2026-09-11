#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_temp_file.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiVlogInfoSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.17: vpi_get_vlog_info() supplies the product and version strings, and
// reports 1 (true) on success. With no invocation options recorded there are
// zero argv entries.
TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsProductAndVersion) {
  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_NE(info.product, nullptr);
  ASSERT_NE(info.version, nullptr);
  EXPECT_STREQ(info.product, "DeltaHDL");
  EXPECT_STREQ(info.version, "0.1.0");
  EXPECT_EQ(info.argc, 0);
}

// §38.17: the routine shall return 0 (false) on failure. A null result
// structure has nowhere to place the information, so the call fails.
TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsZeroOnFailure) {
  EXPECT_EQ(vpi_get_vlog_info(nullptr), 0);
}

// §38.17: argc is the number of invocation options and argv carries their
// values; there shall be argc entries in argv, each a NUL-terminated string,
// and entry zero shall be the tool's name.
TEST_F(VpiVlogInfoSim, GetVlogInfoReportsInvocationCommandLine) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {"-top", "dut", "+define+FOO"});

  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  // There shall be argc entries in argv (tool name plus three options).
  ASSERT_EQ(info.argc, 4);
  ASSERT_NE(info.argv, nullptr);

  // Entry zero shall be the tool's name; the remaining entries are the options
  // in command-line order, each a distinct NUL-terminated string.
  EXPECT_STREQ(info.argv[0], "delta-sim");
  EXPECT_STREQ(info.argv[1], "-top");
  EXPECT_STREQ(info.argv[2], "dut");
  EXPECT_STREQ(info.argv[3], "+define+FOO");
}

// §38.17: the minimal non-empty command line is the tool name alone with no
// invocation options. There shall then be exactly one argv entry, and entry
// zero shall hold the tool's name, with argv still a valid pointer array.
TEST_F(VpiVlogInfoSim, GetVlogInfoReportsToolNameWhenNoOptions) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {});

  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  ASSERT_EQ(info.argc, 1);
  ASSERT_NE(info.argv, nullptr);
  EXPECT_STREQ(info.argv[0], "delta-sim");
}

// §38.17: "The vendor tool may provide a command-line option to pass a file
// containing a set of options. In that case, the argument strings returned by
// vpi_get_vlog_info() shall contain the vendor option string name followed by a
// pointer to a NULL-terminated array of pointers to characters. This new array
// shall contain the parsed contents of the file. The value in entry zero shall
// contain the name of the file. The remaining entries shall contain pointers to
// NULL-terminated character arrays containing the different options in the
// file. The last entry in this array shall be NULL." deltahdl provides that
// option as -f, which src/driver/cli_options.cpp reads, so the report takes
// that shape rather than naming the file and stopping there.
TEST_F(VpiVlogInfoSim, AnOptionsFileIsReportedAsAnArrayOfItsParsedContents) {
  std::string options = "/tmp/deltahdl_3817_options.f";
  SeedFile(options, "--top dut  # the rest of this line is a comment\n-Wall\n");

  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f", options, "-o", "a"});

  SVpiVlogInfo info = {};
  ASSERT_EQ(vpi_get_vlog_info(&info), 1);

  // The command line's own entries: the file name is not among them, the
  // pointer to its array standing where the name was written.
  ASSERT_EQ(info.argc, 5);
  EXPECT_STREQ(info.argv[0], "deltahdl");
  EXPECT_STREQ(info.argv[1], "-f");
  EXPECT_STREQ(info.argv[3], "-o");
  EXPECT_STREQ(info.argv[4], "a");

  // Entry 2 is the pointer the clause describes, not a character array.
  const char* const* file = reinterpret_cast<const char* const*>(info.argv[2]);
  ASSERT_NE(file, nullptr);
  EXPECT_STREQ(file[0], options.c_str());  // entry zero: the file's name
  EXPECT_STREQ(file[1], "--top");
  EXPECT_STREQ(file[2], "dut");
  EXPECT_STREQ(file[3], "-Wall");  // the comment and its line's rest are gone
  EXPECT_EQ(file[4], nullptr);     // the last entry
}

// §38.17: "If one of the options is the vendor file option, then the next
// pointer shall behave the same as previously described." A file that names
// another is reported with an array of its own inside the first one's.
TEST_F(VpiVlogInfoSim, AnOptionsFileThatNamesAnotherNestsTheSameWay) {
  std::string inner = "/tmp/deltahdl_3817_inner.f";
  std::string outer = "/tmp/deltahdl_3817_outer.f";
  SeedFile(inner, "-Werror\n");
  SeedFile(outer, "-f " + inner + "\n");

  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f", outer});

  SVpiVlogInfo info = {};
  ASSERT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_EQ(info.argc, 3);

  const char* const* outer_argv =
      reinterpret_cast<const char* const*>(info.argv[2]);
  ASSERT_NE(outer_argv, nullptr);
  EXPECT_STREQ(outer_argv[0], outer.c_str());
  EXPECT_STREQ(outer_argv[1], "-f");

  const char* const* inner_argv =
      reinterpret_cast<const char* const*>(outer_argv[2]);
  ASSERT_NE(inner_argv, nullptr);
  EXPECT_STREQ(inner_argv[0], inner.c_str());
  EXPECT_STREQ(inner_argv[1], "-Werror");
  EXPECT_EQ(inner_argv[2], nullptr);
  EXPECT_EQ(outer_argv[3], nullptr);
}

// §38.17: the vendor option written with no file after it names none, so there
// is no array to point at and the report holds the option alone.
TEST_F(VpiVlogInfoSim, TheVendorOptionWrittenLastNamesNoFile) {
  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f"});

  SVpiVlogInfo info = {};
  ASSERT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_EQ(info.argc, 2);
  EXPECT_STREQ(info.argv[1], "-f");
}

}  // namespace
}  // namespace delta
