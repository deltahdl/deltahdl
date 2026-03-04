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

}
