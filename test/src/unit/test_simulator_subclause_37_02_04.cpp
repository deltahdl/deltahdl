#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleValiditySim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiHandleValiditySim, FreshHandleIsValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_TRUE(vpi_ctx_.HandleValid(mod));
}

TEST_F(VpiHandleValiditySim, HandleToVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_TRUE(vpi_ctx_.HandleValid(mod));

  mod->object_exists = false;

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_FALSE(vpi_ctx_.HandleReleased(mod));
}

TEST_F(VpiHandleValiditySim, ReleasingOneHandleLeavesDistinctHandleValid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  vpi_ctx_.ReleaseHandle(mod);

  EXPECT_FALSE(vpi_ctx_.HandleValid(mod));
  EXPECT_TRUE(vpi_ctx_.HandleValid(other));
}

TEST_F(VpiHandleValiditySim, NullHandleIsInvalid) {
  EXPECT_FALSE(vpi_ctx_.HandleValid(nullptr));
}

TEST_F(VpiHandleValiditySim, HandleAliasingAVanishedObjectIsInvalid) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(other, mod);
  ASSERT_TRUE(vpi_ctx_.HandleValid(other));

  mod->object_exists = false;

  EXPECT_FALSE(vpi_ctx_.HandleValid(other));
}

TEST_F(VpiHandleValiditySim, ReleasingAnAliasOfAVanishedObjectFails) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* other = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_EQ(vpi_ctx_.ReleaseHandleStatus(other), 1);

  auto* third = vpi_ctx_.CreateHandleFor(mod);
  ASSERT_NE(third, nullptr);
  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(third), 0);
  EXPECT_EQ(vpi_ctx_.ReleaseHandleStatus(mod), 0);
}

TEST_F(VpiHandleValiditySim, NoHandleIsCreatedPastAnObjectsLifetime) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(vpi_ctx_.CreateHandleFor(mod), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_ctx_.CreateHandleFor(mod), nullptr);
}

TEST_F(VpiHandleValiditySim,
       DISABLED_ARelationFromAVanishedObjectGivesNoHandle) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("p", kVpiInput, mod);
  ASSERT_NE(vpi_handle(vpiModule, VpiHandleOf(port)), nullptr);

  port->object_exists = false;

  EXPECT_EQ(vpi_handle(vpiModule, VpiHandleOf(port)), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_ARelationToAVanishedObjectGivesNoHandle) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("p", kVpiInput, mod);
  ASSERT_NE(vpi_handle(vpiModule, VpiHandleOf(port)), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_handle(vpiModule, VpiHandleOf(port)), nullptr);
}

TEST_F(VpiHandleValiditySim,
       DISABLED_AnIterationOfAVanishedObjectGivesNoIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);
  vpiHandle live = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(live, nullptr);
  vpi_release_handle(live);

  mod->object_exists = false;

  EXPECT_EQ(vpi_iterate(vpiPort, VpiHandleOf(mod)), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_AScanPassesOverAVanishedObject) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* gone = vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto* kept = vpi_ctx_.CreatePort("b", kVpiInput, mod);
  vpiHandle it = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(it, nullptr);

  gone->object_exists = false;

  vpiHandle first = vpi_scan(it);
  EXPECT_EQ(VpiObjectOf(first), kept);
  if (first != nullptr) EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_AnIndexIntoAVanishedArrayGivesNoHandle) {
  Variable* e0 = sim_ctx_.CreateVariable("m0", 8);
  Variable* e1 = sim_ctx_.CreateVariable("m1", 8);
  auto* array =
      vpi_ctx_.CreateRegArray("mem", vpiStaticArray, {{0, 1}}, {e0, e1});
  ASSERT_NE(vpi_handle_by_index(VpiHandleOf(array), 1), nullptr);

  array->object_exists = false;

  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(array), 1), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_AVanishedIndexedElementGivesNoHandle) {
  Variable* e0 = sim_ctx_.CreateVariable("m0", 8);
  Variable* e1 = sim_ctx_.CreateVariable("m1", 8);
  auto* array =
      vpi_ctx_.CreateRegArray("mem", vpiStaticArray, {{0, 1}}, {e0, e1});

  array->children[1]->object_exists = false;

  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(array), 1), nullptr);
  EXPECT_NE(vpi_handle_by_index(VpiHandleOf(array), 0), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_AVanishedObjectIsNotFoundByName) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  PLI_BYTE8 name[] = "top";
  ASSERT_NE(vpi_handle_by_name(name, nullptr), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_handle_by_name(name, nullptr), nullptr);
}

TEST_F(VpiHandleValiditySim, DISABLED_NoNameIsFoundThroughAVanishedScope) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);
  PLI_BYTE8 name[] = "p";
  ASSERT_NE(vpi_handle_by_name(name, VpiHandleOf(mod)), nullptr);

  mod->object_exists = false;

  EXPECT_EQ(vpi_handle_by_name(name, VpiHandleOf(mod)), nullptr);
}

TEST_F(VpiHandleValiditySim,
       DISABLED_AMultiIndexThroughAVanishedObjectGivesNoHandle) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  vpi_ctx_.CreatePort("a", kVpiInput, bus);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, bus);
  vpi_ctx_.CreatePort("b0", kVpiOutput, port_b);
  auto* bit_b1 = vpi_ctx_.CreatePort("b1", kVpiOutput, port_b);
  int indices[] = {1, 1};
  ASSERT_NE(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, indices), nullptr);

  port_b->object_exists = false;
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, indices), nullptr);

  port_b->object_exists = true;
  bit_b1->object_exists = false;
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 2, indices), nullptr);
}

TEST_F(VpiHandleValiditySim,
       DISABLED_AVanishedObjectBothReferencesReachGivesNoHandle) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  VpiHandle path = vpi_ctx_.CreateModule("shared", "shared");
  path->type = vpiInterModPath;
  out_port->children.push_back(path);
  in_port->children.push_back(path);
  ASSERT_NE(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                             VpiHandleOf(in_port)),
            nullptr);

  path->object_exists = false;
  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                             VpiHandleOf(in_port)),
            nullptr);

  path->object_exists = true;
  in_port->object_exists = false;
  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                             VpiHandleOf(in_port)),
            nullptr);
}

}  // namespace
}  // namespace delta
