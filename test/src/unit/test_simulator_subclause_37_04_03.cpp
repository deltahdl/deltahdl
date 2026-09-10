#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.4.3 (Diagram key for traversing relationships) says how an arrow in a
// data model diagram is walked. A single arrow is a one-to-one relationship
// "accessed with the routine vpi_handle()" and a double arrow a one-to-many one
// "accessed with the routine vpi_scan()", each written out as the line of an
// application that walks it; a tag on the arrow replaces the target's own type
// in the request; and an arrow that "originates from a circle is traversed
// using NULL for the ref_h". Everything else is drawn from a reference object,
// and the closing sentence gives the untagged request its name: "the type used
// for access is determined by adding 'vpi' to the beginning of the word within
// the enclosure, with each word's first letter being a capital".
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

// Claim (single arrow): a one-to-one relationship is accessed with vpi_handle()
// naming the target's own type, which for the enclosure `module` is vpiModule.
TEST_F(VpiRelationTraversal, AOneToOneRelationIsWalkedWithVpiHandle) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle port = ctx_.CreatePort("p", kVpiInput, mod);

  EXPECT_EQ(vpi_handle(vpiModule, port), mod);
}

// Claim (double arrow): a one-to-many relationship is walked with the iterator
// vpi_iterate() hands back, one object per vpi_scan() - the loop the clause
// writes out, run here over the module's ports.
TEST_F(VpiRelationTraversal, AOneToManyRelationIsWalkedWithVpiScan) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle p0 = ctx_.CreatePort("p0", kVpiInput, mod);
  VpiHandle p1 = ctx_.CreatePort("p1", kVpiOutput, mod);

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiPort, mod));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], p0);
  EXPECT_EQ(seen[1], p1);
}

// Claim (circle, one-to-many): a relationship drawn from a circle is traversed
// with NULL for the ref_h. §37.5 detail 1 draws the top-level modules that way,
// so vpi_iterate(vpiModule, NULL) is what reaches them.
TEST_F(VpiRelationTraversal, ARelationFromACircleIsTraversedWithANullRef) {
  VpiHandle top = ctx_.CreateModule("top", "top");
  top->top_module = true;

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiModule, nullptr));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], top);
}

// Claim: NULL is what a circle means, and a relationship no circle originates
// has nothing to be traversed from. A scope's regs are drawn from the scope, so
// a null reference names no traversal of them and yields no iterator - rather
// than sweeping up every reg of every instance in the run, which is a
// relationship no arrow in any diagram stands for.
TEST_F(VpiRelationTraversal, ARelationFromNoCircleIsNotTraversedFromNull) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiObject reg;
  reg.type = kVpiReg;
  mod->children.push_back(&reg);

  // The relationship itself is there, walked from the scope it is drawn from.
  ASSERT_EQ(ScanAll(vpi_iterate(kVpiReg, mod)).size(), 1u);

  EXPECT_EQ(vpi_iterate(kVpiReg, nullptr), nullptr);
}

// Claim: the same holds of the one-to-one routine, which already answered a
// null reference only for the relationships the diagrams draw from a circle.
// The two routines the key pairs with its two notations agree about what a null
// reference means.
TEST_F(VpiRelationTraversal, TheOneToOneRoutineAgreesAboutANullRef) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  mod->top_module = true;

  EXPECT_EQ(vpi_handle(vpiPort, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
