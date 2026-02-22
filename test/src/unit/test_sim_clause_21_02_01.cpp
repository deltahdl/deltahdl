// §21.2.1: The display and write tasks

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "simulation/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FormatOctal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 8));
  auto out = FormatDisplay("%o", vals);
  EXPECT_EQ(out, "00000000010");
}

TEST(SysTask, FormatReal_e) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%e", vals);
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, FormatReal_f) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%f", vals);
  EXPECT_NE(out.find("2.5"), std::string::npos);
}

TEST(SysTask, FormatString_s) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  uint64_t encoded = (static_cast<uint64_t>('H') << 8) | 'i';
  vals.push_back(MakeLogic4VecVal(arena, 16, encoded));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "Hi");
}

TEST(SysTask, FormatModule_m) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%m", vals);
  EXPECT_FALSE(out.empty());
}

}  // namespace
