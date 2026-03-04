// §21.2.1.7: String format

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FormatString_s) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  uint64_t encoded = (static_cast<uint64_t>('H') << 8) | 'i';
  vals.push_back(MakeLogic4VecVal(arena, 16, encoded));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "Hi");
}

TEST(FormatArg, StringFromAscii) {
  Arena arena;
  // 'A' = 0x41 = 65
  auto val = MakeLogic4VecVal(arena, 8, 65);
  EXPECT_EQ(FormatValueAsString(val), "A");
}

}  // namespace
