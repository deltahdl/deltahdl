#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimeFunctionArguments, DISABLED_ATimeFunctionGivenAnArgumentIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  time a;\n"
      "  real r;\n"
      "  initial a = $time(1);\n"
      "  initial a = $stime($time);\n"
      "  initial r = $realtime(2);\n"
      "endmodule\n",
      f);
  for (const auto& [line, name] :
       std::initializer_list<std::pair<uint32_t, std::string>>{
           {4u, "$time"}, {5u, "$stime"}, {6u, "$realtime"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), name + " takes no argument",
                              line, "20.3"))
        << name;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(TimeFunctionArguments, EachTimeFunctionWrittenBareIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  time a;\n"
      "  real r;\n"
      "  initial a = $time;\n"
      "  initial a = $stime;\n"
      "  initial r = $realtime;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
