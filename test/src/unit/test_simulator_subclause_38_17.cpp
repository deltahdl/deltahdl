#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_temp_file.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

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

TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsProductAndVersion) {
  s_vpi_vlog_info info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_NE(info.product, nullptr);
  ASSERT_NE(info.version, nullptr);
  EXPECT_STREQ(info.product, "DeltaHDL");
  EXPECT_STREQ(info.version, "0.1.0");
  EXPECT_EQ(info.argc, 0);
}

TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsZeroOnFailure) {
  EXPECT_EQ(vpi_get_vlog_info(nullptr), 0);
}

TEST_F(VpiVlogInfoSim, GetVlogInfoReportsInvocationCommandLine) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {"-top", "dut", "+define+FOO"});

  s_vpi_vlog_info info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  ASSERT_EQ(info.argc, 4);
  ASSERT_NE(info.argv, nullptr);

  EXPECT_STREQ(info.argv[0], "delta-sim");
  EXPECT_STREQ(info.argv[1], "-top");
  EXPECT_STREQ(info.argv[2], "dut");
  EXPECT_STREQ(info.argv[3], "+define+FOO");
}

TEST_F(VpiVlogInfoSim, GetVlogInfoReportsToolNameWhenNoOptions) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {});

  s_vpi_vlog_info info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  ASSERT_EQ(info.argc, 1);
  ASSERT_NE(info.argv, nullptr);
  EXPECT_STREQ(info.argv[0], "delta-sim");
}

TEST_F(VpiVlogInfoSim, AnOptionsFileIsReportedAsAnArrayOfItsParsedContents) {
  std::string options = "/tmp/deltahdl_3817_options.f";
  SeedFile(options, "--top dut  # the rest of this line is a comment\n-Wall\n");

  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f", options, "-o", "a"});

  s_vpi_vlog_info info = {};
  ASSERT_EQ(vpi_get_vlog_info(&info), 1);

  ASSERT_EQ(info.argc, 5);
  EXPECT_STREQ(info.argv[0], "deltahdl");
  EXPECT_STREQ(info.argv[1], "-f");
  EXPECT_STREQ(info.argv[3], "-o");
  EXPECT_STREQ(info.argv[4], "a");

  const char* const* file = reinterpret_cast<const char* const*>(info.argv[2]);
  ASSERT_NE(file, nullptr);
  EXPECT_STREQ(file[0], options.c_str());
  EXPECT_STREQ(file[1], "--top");
  EXPECT_STREQ(file[2], "dut");
  EXPECT_STREQ(file[3], "-Wall");
  EXPECT_EQ(file[4], nullptr);
}

TEST_F(VpiVlogInfoSim, AnOptionsFileThatNamesAnotherNestsTheSameWay) {
  std::string inner = "/tmp/deltahdl_3817_inner.f";
  std::string outer = "/tmp/deltahdl_3817_outer.f";
  SeedFile(inner, "-Werror\n");
  SeedFile(outer, "-f " + inner + "\n");

  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f", outer});

  s_vpi_vlog_info info = {};
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

TEST_F(VpiVlogInfoSim, TheVendorOptionWrittenLastNamesNoFile) {
  vpi_ctx_.SetInvocationArguments("deltahdl", {"-f"});

  s_vpi_vlog_info info = {};
  ASSERT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_EQ(info.argc, 2);
  EXPECT_STREQ(info.argv[1], "-f");
}

}  // namespace
}  // namespace delta
