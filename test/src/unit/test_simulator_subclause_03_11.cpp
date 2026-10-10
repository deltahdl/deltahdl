#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §3.11 (printed page 55) with §23.3.1 and §24.3: a module or program
// instantiated nowhere is an implicit top-level instance, and one an interface
// instantiates (A.1.6 reaches program_instantiation from interface_item) is
// instantiated. p is instantiated in bus, so top alone roots the design; p was
// made a top too and its initial block ran twice.
TEST(ImplicitTopLevelInstances, ProgramInstantiatedInAnInterfaceIsNoTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "program p; initial $display(\"%m\"); endprogram\n"
      "interface bus; p u(); endinterface\n"
      "module top; bus b(); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

}  // namespace
