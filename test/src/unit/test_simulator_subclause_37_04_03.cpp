#include <gtest/gtest.h>

#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiRelationTraversal : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiRelationTraversal, AOneToOneRelationIsWalkedWithVpiHandle) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle port = ctx_.CreatePort("p", kVpiInput, mod);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, VpiHandleOf(port))), mod);
}

TEST_F(VpiRelationTraversal, AOneToManyRelationIsWalkedWithVpiScan) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle p0 = ctx_.CreatePort("p0", kVpiInput, mod);
  VpiHandle p1 = ctx_.CreatePort("p1", kVpiOutput, mod);

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiPort, VpiHandleOf(mod)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), p0);
  EXPECT_EQ(VpiObjectOf(seen[1]), p1);
}

TEST_F(VpiRelationTraversal, ARelationFromACircleIsTraversedWithANullRef) {
  VpiHandle top = ctx_.CreateModule("top", "top");
  top->top_module = true;

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiModule, nullptr));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), top);
}

TEST_F(VpiRelationTraversal, ARelationFromNoCircleIsNotTraversedFromNull) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiObject reg;
  reg.type = kVpiReg;
  mod->children.push_back(&reg);

  ASSERT_EQ(ScanAll(vpi_iterate(kVpiReg, VpiHandleOf(mod))).size(), 1u);

  EXPECT_EQ(vpi_iterate(kVpiReg, nullptr), nullptr);
}

TEST_F(VpiRelationTraversal, TheOneToOneRoutineAgreesAboutANullRef) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  mod->top_module = true;

  EXPECT_EQ(vpi_handle(vpiPort, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
