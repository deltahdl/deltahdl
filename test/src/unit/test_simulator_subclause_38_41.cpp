#include <gtest/gtest.h>

#include <cstdarg>
#include <cstdio>
#include <string>

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

PLI_INT32 CallWithStartedVarargs(const char* format, ...) {
  va_list ap;
  va_start(ap, format);
  PLI_INT32 written = vpi_vprintf(const_cast<PLI_BYTE8*>(format), ap);
  va_end(ap);
  return written;
}

class VpiVprintfSim : public ::testing::Test {
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

TEST_F(VpiVprintfSim,
       ConsumesAnAlreadyStartedVarargsListWritingBothDestinations) {
  PLI_INT32 written = CallWithStartedVarargs("value=%d name=%s", 42, "ok");

  const std::string kExpected = "value=42 name=ok";
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), kExpected);
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), kExpected);
  EXPECT_EQ(written, static_cast<PLI_INT32>(kExpected.size()));
}

TEST_F(VpiVprintfSim, ReturnsEofWhenFormatStringIsMissing) {
  EXPECT_EQ(CallWithStartedVarargs(nullptr), EOF);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

TEST_F(VpiVprintfSim, EmptyFormatStringWritesNothingAndReturnsZero) {
  PLI_INT32 written = CallWithStartedVarargs("");

  EXPECT_EQ(written, 0);
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

TEST_F(VpiVprintfSim, PerformsTheSameFunctionAsVpiPrintf) {
  PLI_INT32 by_vprintf = CallWithStartedVarargs("count=%d of %s", 7, "ten");
  const std::string kChannelByVprintf = vpi_ctx_.OutputChannelBuffer();
  const std::string kLogByVprintf = vpi_ctx_.LogFileBuffer();
  ASSERT_FALSE(kChannelByVprintf.empty());

  VpiContext printf_ctx;
  SetGlobalVpiContext(&printf_ctx);
  PLI_INT32 by_printf =
      vpi_printf(const_cast<PLI_BYTE8*>("count=%d of %s"), 7, "ten");

  EXPECT_EQ(by_vprintf, by_printf);
  EXPECT_EQ(kChannelByVprintf, printf_ctx.OutputChannelBuffer());
  EXPECT_EQ(kLogByVprintf, printf_ctx.LogFileBuffer());
}

TEST_F(VpiVprintfSim, ReturnsTheLengthOfTheExpansionRatherThanOfTheFormat) {
  PLI_INT32 written = CallWithStartedVarargs("n=%d", 1000);

  const std::string kExpected = "n=1000";
  EXPECT_EQ(written, static_cast<PLI_INT32>(kExpected.size()));
  EXPECT_NE(written, static_cast<PLI_INT32>(std::string("n=%d").size()));
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), kExpected);
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), kExpected);
}

}  // namespace
}  // namespace delta
