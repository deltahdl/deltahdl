// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string_view>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(SvaEngine, SeverityToString) {
  EXPECT_EQ(SeverityToString(AssertionSeverity::kInfo), "INFO");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kWarning), "WARNING");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kError), "ERROR");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kFatal), "FATAL");
}

TEST(SvaEngine, SeverityDefaultIsError) {
  AssertionSeverity sev = AssertionSeverity::kError;
  EXPECT_EQ(SeverityToString(sev), "ERROR");
}

}  // namespace
