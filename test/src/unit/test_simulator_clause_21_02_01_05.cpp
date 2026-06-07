#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// §21.2.1.5 Hierarchical name format. The %m format specifier takes no argument
// and expands to the hierarchical name of the design element, subroutine, named
// block, or labeled statement that invokes the system task carrying it. These
// tests drive the full simulator ($display passes the run-time context into the
// formatter in eval_format.cpp, which builds the name from the running process's
// instance path and the active subroutine / named-block scopes) and capture the
// displayed text end to end.

namespace {

// §21.2.1.5 (C2): invoked directly from a top-level module, %m reports that
// module's name, the root of the design-element hierarchy.
TEST(HierarchicalNameFormat, TopLevelModuleName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial $display(\"%m\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip\n");
}

// §21.2.1.5 (C1): %m accepts no argument. With a following %0d specifier and a
// single expression supplied, %m expands to the scope name without consuming the
// expression, leaving it for %0d. If %m had drawn an argument, the decimal field
// would have nothing to print.
TEST(HierarchicalNameFormat, PercentMConsumesNoArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    $display(\"%m=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip=42\n");
}

// §21.2.1.5 (C2): named blocks are part of the hierarchy, each contributing a
// level reported in lexical-nesting order from the outermost scope inward. The
// nested case also covers the single-block append as its first level.
TEST(HierarchicalNameFormat, NestedNamedBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      $display(\"%m\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.outer.inner\n");
}

// §21.2.1.5 (C2): a subroutine is a hierarchy level too. When the task that
// calls $display is itself invoked from the module, %m names the task within the
// module.
TEST(HierarchicalNameFormat, SubroutineScopeInHierarchy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module chip;\n"
      "  task show;\n"
      "    $display(\"%m\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.show\n");
}

// §21.2.1.5 (C2): for a system task running inside an instantiated submodule, %m
// reports the full instance path -- the top module name followed by the instance
// name, not the submodule's type name. This is the case the subclause
// highlights: distinguishing among many instances of the same module.
TEST(HierarchicalNameFormat, ChildInstancePathReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  initial $display(\"%m\");\n"
      "endmodule\n"
      "module chip;\n"
      "  leaf u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.u1\n");
}

// §21.2.1.5 (C2) edge: the instance path and an inner subroutine scope compose
// into one name. A task that runs $display inside an instantiated submodule
// contributes both the instance level and the subroutine level, joined in order:
// top module, instance, task. This is the only case that exercises a non-empty
// instance prefix and an active scope together, observing the separator between
// the two contributions.
TEST(HierarchicalNameFormat, SubroutineWithinInstanceComposesPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  task show;\n"
      "    $display(\"%m\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n"
      "module chip;\n"
      "  leaf u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "chip.u1.show\n");
}

}  // namespace
