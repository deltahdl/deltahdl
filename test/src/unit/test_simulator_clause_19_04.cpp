// §19.4: Using covergroups in classes

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.3: Covergroup in class (CoverGroup is independent, can be embedded)
// =============================================================================
TEST(Coverage, CoverGroupAsClassMember) {
  // Simulates a covergroup embedded in a class: just a struct.
  struct MyClass {
    CoverageDB db;
    CoverGroup *cg = nullptr;
    void Init() { cg = db.CreateGroup("cg_in_class"); }
  };
  MyClass obj;
  obj.Init();
  ASSERT_NE(obj.cg, nullptr);
  EXPECT_EQ(obj.cg->name, "cg_in_class");
}

}  // namespace
