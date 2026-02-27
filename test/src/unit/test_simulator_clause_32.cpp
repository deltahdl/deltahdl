// §32: (MSB) is reserved to represent a file descriptor (fd) returned from the
// SystemVerilog $fopen system

#include "simulation/specify.h"
#include "fixture_specify.h"

namespace {

// =============================================================================
// §32 SDF annotation (runtime model)
// =============================================================================
TEST_F(SpecifyTest, SdfAnnotateModel) {
  // Test the runtime SpecifyManager SDF annotation support.
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", "top.dut"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut");
}

}  // namespace
