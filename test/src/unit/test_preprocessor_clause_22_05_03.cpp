#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, UndefineAll) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undefineall\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

}
