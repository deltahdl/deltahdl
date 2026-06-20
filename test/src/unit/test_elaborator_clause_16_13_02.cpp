#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/multiclock_property.h"

using namespace delta;

namespace {

// §16.13.2: a property whose subproperties all share the property clock and are
// not multiclocked sequences is singly clocked, not multiclocked.
TEST(MulticlockProperty, AllSubpropertiesShareClockIsSinglyClocked) {
  const std::vector<std::string> subproperty_clocks = {"clk", "clk"};
  EXPECT_FALSE(IsMulticlockedProperty(
      /*property_clock=*/"clk", subproperty_clocks,
      /*any_subproperty_is_multiclocked_sequence=*/false));
}

// §16.13.2: the property is multiclocked when some subproperty is governed by a
// clock different from the property clock. Mirrors `(@(posedge clk0) sig0) and
// (@(posedge clk1) sig1)` viewed from the clk0 property clock.
TEST(MulticlockProperty, SubpropertyOnDifferentClockIsMulticlocked) {
  const std::vector<std::string> subproperty_clocks = {"clk0", "clk1"};
  EXPECT_TRUE(IsMulticlockedProperty(
      /*property_clock=*/"clk0", subproperty_clocks,
      /*any_subproperty_is_multiclocked_sequence=*/false));
}

// §16.13.2: a multiclocked-sequence subproperty makes the enclosing property
// multiclocked even when every explicit subproperty clock matches the property
// clock. Mirrors `@(posedge clk0) sig0 ##1 @(posedge clk1) sig1` used as a
// property.
TEST(MulticlockProperty, MulticlockedSequenceSubpropertyIsMulticlocked) {
  const std::vector<std::string> subproperty_clocks = {"clk", "clk"};
  EXPECT_TRUE(IsMulticlockedProperty(
      /*property_clock=*/"clk", subproperty_clocks,
      /*any_subproperty_is_multiclocked_sequence=*/true));
}

// §16.13.2: a property with no subproperty clocks and no multiclocked sequence
// is not multiclocked — the leading singly clocked degenerate case.
TEST(MulticlockProperty, NoSubpropertiesIsSinglyClocked) {
  EXPECT_FALSE(IsMulticlockedProperty(
      /*property_clock=*/"clk", /*subproperty_clocks=*/{},
      /*any_subproperty_is_multiclocked_sequence=*/false));
}

// §16.13.2: a differing clock anywhere in the subproperty list is enough; the
// scan does not stop at the first matching clock.
TEST(MulticlockProperty, DifferingClockAfterMatchingClockIsMulticlocked) {
  const std::vector<std::string> subproperty_clocks = {"clk0", "clk0", "clk2"};
  EXPECT_TRUE(IsMulticlockedProperty(
      /*property_clock=*/"clk0", subproperty_clocks,
      /*any_subproperty_is_multiclocked_sequence=*/false));
}

// §16.13.2 edge case: a multiclocked-sequence subproperty makes the property
// multiclocked even when no explicit subproperty clocks are listed, so the
// sequence flag dominates the empty clock scan.
TEST(MulticlockProperty,
     MulticlockedSequenceWithoutListedClocksIsMulticlocked) {
  EXPECT_TRUE(IsMulticlockedProperty(
      /*property_clock=*/"clk", /*subproperty_clocks=*/{},
      /*any_subproperty_is_multiclocked_sequence=*/true));
}

}  // namespace
