#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/multiclock_property.h"

using namespace delta;

namespace {

TEST(MulticlockProperty, AllSubpropertiesShareClockIsSinglyClocked) {
  const std::vector<std::string> kSubpropertyClocks = {"clk", "clk"};
  EXPECT_FALSE(IsMulticlockedProperty("clk", kSubpropertyClocks, false));
}

TEST(MulticlockProperty, SubpropertyOnDifferentClockIsMulticlocked) {
  const std::vector<std::string> kSubpropertyClocks = {"clk0", "clk1"};
  EXPECT_TRUE(IsMulticlockedProperty("clk0", kSubpropertyClocks, false));
}

TEST(MulticlockProperty, MulticlockedSequenceSubpropertyIsMulticlocked) {
  const std::vector<std::string> kSubpropertyClocks = {"clk", "clk"};
  EXPECT_TRUE(IsMulticlockedProperty("clk", kSubpropertyClocks, true));
}

TEST(MulticlockProperty, NoSubpropertiesIsSinglyClocked) {
  EXPECT_FALSE(IsMulticlockedProperty("clk", {}, false));
}

TEST(MulticlockProperty, DifferingClockAfterMatchingClockIsMulticlocked) {
  const std::vector<std::string> kSubpropertyClocks = {"clk0", "clk0", "clk2"};
  EXPECT_TRUE(IsMulticlockedProperty("clk0", kSubpropertyClocks, false));
}

TEST(MulticlockProperty,
     MulticlockedSequenceWithoutListedClocksIsMulticlocked) {
  EXPECT_TRUE(IsMulticlockedProperty("clk", {}, true));
}

}  // namespace
