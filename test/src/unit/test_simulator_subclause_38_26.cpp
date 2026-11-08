#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_run_files.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiMcdNameSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;

  static constexpr PLI_UINT32 kMsbChannel = 0x80000000u;
};

TEST_F(VpiMcdNameSim, ReturnsNameOfFileNamedByDescriptor) {
  char name[] = "trace.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  PLI_BYTE8* reported = vpi_mcd_name(mcd);
  ASSERT_NE(reported, nullptr);
  EXPECT_STREQ(reported, "trace.log");
}

TEST_F(VpiMcdNameSim, ReportsNameOfFopenFileIncludingFdWithMsbSet) {
  PLI_UINT32 fd = kMsbChannel | 0x5u;
  vpi_ctx_.RegisterFopenMcdFile("from_fopen.log", fd);

  PLI_BYTE8* reported = vpi_mcd_name(fd);
  ASSERT_NE(reported, nullptr);
  EXPECT_STREQ(reported, "from_fopen.log");
}

TEST_F(VpiMcdNameSim, ReturnsNullOnError) {
  EXPECT_EQ(vpi_mcd_name(0u), nullptr);

  EXPECT_EQ(vpi_mcd_name(0x00000008u), nullptr);
}

TEST_F(VpiMcdNameSim, OverwritesReturnedValueOnSubsequentCalls) {
  char a[] = "alpha.log";
  char b[] = "bravo.log";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  PLI_BYTE8* first = vpi_mcd_name(mcd_a);
  ASSERT_NE(first, nullptr);
  std::string retained(first);
  EXPECT_EQ(retained, "alpha.log");

  PLI_BYTE8* second = vpi_mcd_name(mcd_b);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second, first);
  EXPECT_STREQ(first, "bravo.log");
  EXPECT_EQ(retained, "alpha.log");
}

TEST_F(VpiMcdNameSim, AMultiChannelDescriptorNamesNoOneFile) {
  char first[] = "first.log";
  char second[] = "second.log";
  PLI_UINT32 mcd_first = vpi_mcd_open(first);
  PLI_UINT32 mcd_second = vpi_mcd_open(second);
  ASSERT_NE(mcd_first, 0u);
  ASSERT_NE(mcd_second, 0u);
  ASSERT_STREQ(vpi_mcd_name(mcd_first), "first.log");
  ASSERT_STREQ(vpi_mcd_name(mcd_second), "second.log");

  EXPECT_EQ(vpi_mcd_name(mcd_first | mcd_second), nullptr);
}

std::string fd_name;
std::string mcd_name;
bool unopened_named = true;

class NameOfAFopenedFile : public RunFilesRun {
 protected:
  static std::string NameOf(PLI_UINT32 cd) {
    const char* name = vpi_mcd_name(cd);
    return name == nullptr ? "" : name;
  }
  static PLI_INT32 NameBoth(PLI_BYTE8*) {
    fd_name = NameOf(DescriptorIn("top.fd"));
    mcd_name = NameOf(DescriptorIn("top.mcd"));
    return 0;
  }
  static PLI_INT32 NameUnopened(PLI_BYTE8*) {
    unopened_named = vpi_mcd_name(PLI_UINT32{1} << 20) != nullptr;
    return 0;
  }
};

TEST_F(NameOfAFopenedFile, BothFormsAreNamed) {
  RegisterTask("$name_both", &NameBoth);
  Run("module top; integer fd, mcd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"named_fd.txt\", \"w\");\n"
      "    mcd = $fopen(\"named_mcd.txt\");\n"
      "    $name_both;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(fd_name, "named_fd.txt");
  EXPECT_EQ(mcd_name, "named_mcd.txt");
}

TEST_F(NameOfAFopenedFile, AChannelWithNoFileIsNamedNothing) {
  RegisterTask("$name_unopened", &NameUnopened);
  Run("module top; initial $name_unopened; endmodule\n");
  EXPECT_FALSE(unopened_named);
}

}  // namespace
}  // namespace delta
