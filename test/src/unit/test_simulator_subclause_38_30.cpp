#include <gtest/gtest.h>

#include <cstdio>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiPrintfSim : public ::testing::Test {
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

TEST_F(VpiPrintfSim,
       WritesExpandedTextToOutputChannelAndLogFileReturningCount) {
  PLI_BYTE8 format[] = "value=%d name=%s";
  int written = vpi_printf(format, 42, "ok");

  const std::string kExpected = "value=42 name=ok";
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), kExpected);
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), kExpected);
  EXPECT_EQ(written, static_cast<int>(kExpected.size()));
}

TEST_F(VpiPrintfSim, ReturnsEofWhenFormatStringIsMissing) {
  EXPECT_EQ(vpi_printf(nullptr), EOF);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

TEST_F(VpiPrintfSim, EmptyFormatWritesNothingAndReturnsZero) {
  PLI_BYTE8 format[] = "";
  int written = vpi_printf(format);

  EXPECT_EQ(written, 0);
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

TEST_F(VpiPrintfSim, EachCallAddsItsTextAfterTheLastOnBothDestinations) {
  PLI_BYTE8 first[] = "one ";
  PLI_BYTE8 second[] = "two=%d";
  vpi_printf(first);

  int written = vpi_printf(second, 2);

  EXPECT_EQ(written, 5);
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "one two=2");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "one two=2");
}

TEST_F(VpiPrintfSim, WhatWasPrintedIsWhatAFlushOfTheToolsChannelsCommits) {
  PLI_BYTE8 format[] = "pending=%s";
  vpi_printf(format, "yes");

  ASSERT_EQ(vpi_flush(), 0);

  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "pending=yes");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "pending=yes");
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

}  // namespace
}  // namespace delta
