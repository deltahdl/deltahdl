#include "fixture_specify.h"
#include "simulator/specify.h"

namespace {

TEST_F(SpecifyTest, SdfAnnotateModel) {

  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", "top.dut"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut");
}

}
