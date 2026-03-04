#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FormatModule_m) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%m", vals);
  EXPECT_FALSE(out.empty());
}

}
