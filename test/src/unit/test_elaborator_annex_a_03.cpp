#include <cstddef>
#include <string>

#include "fixture_elaborator.h"

using namespace delta;

// A.3 "Primitive instances" writes no production of its own. It is a heading
// over A.3.1's instantiation forms, A.3.2's pull strengths, A.3.3's terminals
// and A.3.4's type keywords, and what it has to say is that those four make one
// declaration: a keyword A.3.4 names takes the instance shape A.3.1 pairs with
// its group, and the `[ name_of_instance ]` every one of those forms opens with
// is the same name, carrying the range §28.3.5 reads as "the instance array's
// size".
//
// That range is the crossing no subsection file makes, because how many
// primitives a declaration builds is a question only A.3.1's `name_of_instance`
// and the elaborated design answer together. The count is the range's, whatever
// the terminals are: §28.3.6 connects a terminal as wide as the array a bit to
// each element and connects a narrower one whole to every element, so a
// terminal width says how an instance is wired and never how many there are.

namespace {

// How many continuous assignments the module's gates were elaborated into, one
// per driven primitive output.
size_t AssignCount(const RtlirModule* mod) { return mod->assigns.size(); }

const RtlirModule* ElaborateTop(const std::string& src, ElabFixture& f) {
  auto* design = Elaborate(src, f);
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// The range declares four instances and the terminals are scalar, so §28.3.6
// connects each terminal whole to every element: four gates, all driving the
// one wire from the one pair of inputs. Counted off the widest terminal the
// array was one instance, and the three the range declared past the first were
// never built.
TEST(PrimitiveInstanceElaboration, ScalarTerminalsStillBuildTheWholeArray) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 4u);
}

// The bounds are read in either order and are not required to start at zero:
// §28.3.5's size is the count of values they span, which is five here.
TEST(PrimitiveInstanceElaboration, TheRangeBoundsSpanTheInstanceCount) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nand g[7:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 5u);
}

// A.3.1 gives every group of A.3.4's keywords the same `[ name_of_instance ]`,
// so the count is the range's for a switch as much as for a logic gate. A
// three-terminal enable gate over a four-instance array of scalar terminals is
// four instances.
TEST(PrimitiveInstanceElaboration, TheRangeCountsInstancesForEveryGroup) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif1 g[3:0](y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 4u);
}

// A.3.1's `pull_gate_instance` takes the range too, and its one terminal is an
// output: `pulldown p[2:0] (y);` is three pull gates on the one wire.
TEST(PrimitiveInstanceElaboration, APullGateArrayBuildsOnePullPerElement) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y;\n"
      "  pulldown p[2:0](y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 3u);
}

// A declaration with no range is the one instance it is: `name_of_instance`
// carries no dimension, so there is no array to expand. Nor does a range whose
// bounds are equal declare more than the one §28.3.5 counts them as spanning.
// Two such declarations are two instances and no more.
TEST(PrimitiveInstanceElaboration, NoRangeAndAnEqualBoundedRangeAreOneEach) {
  ElabFixture f;
  const auto* mod = ElaborateTop(
      "module m;\n"
      "  wire y, z, a, b;\n"
      "  and g1(y, a, b);\n"
      "  and g2[5:5](z, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(AssignCount(mod), 2u);
}

}  // namespace
