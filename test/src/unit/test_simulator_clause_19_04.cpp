#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, CoverGroupAsClassMember) {
  struct MyClass {
    CoverageDB db;
    CoverGroup* cg = nullptr;
    void Init() { cg = db.CreateGroup("cg_in_class"); }
  };
  MyClass obj;
  obj.Init();
  ASSERT_NE(obj.cg, nullptr);
  EXPECT_EQ(obj.cg->name, "cg_in_class");
}

// §19.4: an embedded covergroup is created only when the new() method assigns
// the result of new() to its variable. If that assignment is absent the
// covergroup is not created and no data is sampled. The constructor decides at
// run time whether to instantiate; without instantiation no group exists.
TEST(Coverage, UninstantiatedCoverGroupNotCreated) {
  struct MyClass {
    CoverageDB db;
    CoverGroup* cg = nullptr;
    explicit MyClass(bool instantiate) {
      if (instantiate) cg = db.CreateGroup("cg");
    }
  };

  MyClass without(false);
  EXPECT_EQ(without.cg, nullptr);
  EXPECT_EQ(without.db.GroupCount(), 0u);

  MyClass with(true);
  ASSERT_NE(with.cg, nullptr);
  EXPECT_EQ(with.db.GroupCount(), 1u);
}

}  // namespace
