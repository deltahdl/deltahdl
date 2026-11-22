#include <gtest/gtest.h>

#include <cstring>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiCompareObjectsSim : public ::testing::Test {
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

TEST_F(VpiCompareObjectsSim, SameHandleComparesEqual) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(mod), VpiHandleOf(mod)), 1);
}

TEST_F(VpiCompareObjectsSim, DifferentObjectsCompareUnequal) {
  auto* a = vpi_ctx_.CreateModule("a", "a");
  auto* b = vpi_ctx_.CreateModule("b", "b");

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(a), VpiHandleOf(b)), 0);
}

TEST_F(VpiCompareObjectsSim,
       AliasingHandlesCompareEqualDespiteDistinctPointers) {
  auto* bit = vpi_ctx_.CreateParameter("ps_bit", 0);
  auto* ps_index = vpi_ctx_.CreateParameter("ps_0", 0);
  auto* member_bit = vpi_ctx_.CreateParameter("ps_b_7", 0);
  ps_index->same_object_as = bit;
  member_bit->same_object_as = bit;

  ASSERT_NE(ps_index, member_bit);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(ps_index), VpiHandleOf(member_bit)),
            1);
}

TEST_F(VpiCompareObjectsSim, ExpressionHandleTracksResolvedElement) {
  auto* i0 = vpi_ctx_.CreateParameter("i_0", 0);
  auto* i1 = vpi_ctx_.CreateParameter("i_1", 0);
  auto* obj2 = vpi_ctx_.CreateParameter("i_0_iter", 0);
  obj2->same_object_as = i0;

  auto* obj1 = vpi_ctx_.CreateParameter("i_j", 0);
  obj1->same_object_as = i0;
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(obj1), VpiHandleOf(obj2)), 1);

  obj1->same_object_as = i1;
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(obj1), VpiHandleOf(obj2)), 0);
}

TEST_F(VpiCompareObjectsSim, AbsentObjectsCompareUnequal) {
  auto* c_a = vpi_ctx_.CreateParameter("c_a", 0);
  auto* d_a = vpi_ctx_.CreateParameter("d_a", 0);
  c_a->object_exists = false;
  d_a->object_exists = false;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(c_a), VpiHandleOf(d_a)), 0);
}

TEST_F(VpiCompareObjectsSim, OneExistentOneAbsentCompareUnequal) {
  auto* c_a = vpi_ctx_.CreateParameter("c_a", 0);
  auto* d_a = vpi_ctx_.CreateParameter("d_a", 0);
  c_a->object_exists = true;
  d_a->object_exists = false;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(c_a), VpiHandleOf(d_a)), 0);
}

TEST_F(VpiCompareObjectsSim, TransitiveAliasResolvesToSameObject) {
  auto* underlying = vpi_ctx_.CreateParameter("underlying", 0);
  auto* mid = vpi_ctx_.CreateParameter("mid", 0);
  auto* first = vpi_ctx_.CreateParameter("first", 0);
  auto* second = vpi_ctx_.CreateParameter("second", 0);

  mid->same_object_as = underlying;
  first->same_object_as = mid;
  second->same_object_as = underlying;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(first), VpiHandleOf(second)), 1);
}

TEST_F(VpiCompareObjectsSim, AliasToAbsentObjectComparesUnequal) {
  auto* underlying = vpi_ctx_.CreateParameter("underlying", 0);
  underlying->object_exists = false;

  auto* alias_a = vpi_ctx_.CreateParameter("alias_a", 0);
  auto* alias_b = vpi_ctx_.CreateParameter("alias_b", 0);
  alias_a->same_object_as = underlying;
  alias_b->same_object_as = underlying;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(alias_a), VpiHandleOf(alias_b)), 0);
}

TEST_F(VpiCompareObjectsSim, NullHandleNeverCompareEqual) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  EXPECT_EQ(vpi_compare_objects(nullptr, VpiHandleOf(mod)), 0);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(mod), nullptr), 0);
  EXPECT_EQ(vpi_compare_objects(nullptr, nullptr), 0);
}

TEST_F(VpiCompareObjectsSim, TwoObjectsOnOneVariableAreTheSameObject) {
  auto* storage = sim_ctx_.CreateVariable("v", 8);
  ASSERT_NE(storage, nullptr);

  auto* first = vpi_ctx_.CreateParameter("first", 0);
  first->var = storage;
  auto* second = vpi_ctx_.CreateParameter("second", 0);
  second->var = storage;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(first), VpiHandleOf(second)), 1);
}

TEST_F(VpiCompareObjectsSim, TwoObjectsOnOneNetAreTheSameObject) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* first = vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto* second = vpi_ctx_.CreatePort("b", kVpiInput, mod);

  Net net;
  first->net = &net;
  second->net = &net;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(first), VpiHandleOf(second)), 1);
}

TEST_F(VpiCompareObjectsSim, ObjectsOnDifferentStorageAreDifferentObjects) {
  auto* one = sim_ctx_.CreateVariable("one", 8);
  auto* other = sim_ctx_.CreateVariable("other", 8);
  ASSERT_NE(one, nullptr);
  ASSERT_NE(other, nullptr);

  auto* first = vpi_ctx_.CreateParameter("first", 0);
  first->var = one;
  auto* second = vpi_ctx_.CreateParameter("second", 0);
  second->var = other;

  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(first), VpiHandleOf(second)), 0);
}

std::vector<int> compared;

PLI_INT32 CompareArgumentsCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle args = vpi_iterate(vpiArgument, call);
  vpiHandle first = vpi_scan(args);
  vpiHandle second = vpi_scan(args);
  vpi_release_handle(args);
  compared.push_back(vpi_compare_objects(first, second));
  return 0;
}

class VpiCompareObjectsRun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    compared.clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$cmp");
    data.calltf = &CompareArgumentsCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

TEST_F(VpiCompareObjectsRun, BitsOfOneVectorAreDifferentObjects) {
  Run("module top; wire [3:0] w; logic [3:0] v; initial $noop; endmodule");
  for (const char* name : {"top.w", "top.v"}) {
    vpiHandle vec = By(name);
    ASSERT_NE(vec, nullptr) << name;
    vpiHandle bit0 = vpi_handle_by_index(vec, 0);
    vpiHandle bit1 = vpi_handle_by_index(vec, 1);
    ASSERT_NE(bit0, nullptr) << name;
    ASSERT_NE(bit1, nullptr) << name;
    EXPECT_EQ(vpi_compare_objects(bit0, bit1), 0) << name;
    EXPECT_EQ(vpi_compare_objects(bit0, vec), 0) << name;
  }
  vpiHandle by_index = vpi_handle_by_index(By("top.w"), 2);
  vpiHandle by_name = By("top.w[2]");
  ASSERT_NE(by_index, nullptr);
  ASSERT_NE(by_name, nullptr);
  EXPECT_EQ(vpi_compare_objects(by_index, by_name), 1);
}

TEST_F(VpiCompareObjectsRun, PackedStructBitAndMemberBitAreOneObject) {
  Run("module top; struct packed { int a; reg [0:7] b; } ps; "
      "initial $noop; endmodule");
  vpiHandle ps = By("top.ps");
  vpiHandle member = By("top.ps.b");
  ASSERT_NE(ps, nullptr);
  ASSERT_NE(member, nullptr);
  vpiHandle member_bit = vpi_handle_by_index(member, 7);
  vpiHandle ps0 = vpi_handle_by_index(ps, 0);
  vpiHandle ps1 = vpi_handle_by_index(ps, 1);
  ASSERT_NE(member_bit, nullptr);
  ASSERT_NE(ps0, nullptr);
  ASSERT_NE(ps1, nullptr);
  EXPECT_EQ(vpi_compare_objects(ps0, member_bit), 1);
  EXPECT_EQ(vpi_compare_objects(ps1, member_bit), 0);
  EXPECT_EQ(vpi_compare_objects(member, By("top.ps.a")), 0);
}

TEST_F(VpiCompareObjectsRun, VarSelectIsTheElementItsIndexNamesNow) {
  Run("module top; integer i [0:3]; int j; initial begin "
      "j = 0; $cmp(i[j], i[0]); j = 1; $cmp(i[j], i[0]); end endmodule");
  EXPECT_EQ(compared, (std::vector<int>{1, 0}));
}

TEST_F(VpiCompareObjectsRun, ClassMemberReferencesFollowTheirHandles) {
  Run("module top; class C; int a; endclass C c, d; initial begin "
      "$cmp(c.a, d.a); c = new; $cmp(c.a, d.a); d = c; $cmp(c.a, d.a); "
      "c = new; $cmp(c.a, d.a); end endmodule");
  EXPECT_EQ(compared, (std::vector<int>{0, 0, 1, 0}));
}

vpiHandle ObjectProperty(const char* class_var, const char* name) {
  vpiHandle obj =
      vpi_handle(vpiClassObj, vpi_handle_by_name(VpiText(class_var), nullptr));
  vpiHandle it = obj != nullptr ? vpi_iterate(vpiVariables, obj) : nullptr;
  if (it == nullptr) return nullptr;
  while (vpiHandle var = vpi_scan(it)) {
    if (std::strcmp(vpi_get_str(vpiName, var), name) == 0) {
      vpi_release_handle(it);
      return var;
    }
  }
  return nullptr;
}

TEST_F(VpiCompareObjectsRun, AMemberReferenceIsItsObjectsPropertyVariable) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$cmp_property");
  data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
    vpiHandle args =
        vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
    vpiHandle reference = vpi_scan(args);
    vpi_release_handle(args);
    compared.push_back(
        vpi_compare_objects(reference, ObjectProperty("top.c", "a")));
    return 0;
  };
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; class C; int a; endclass C c; initial begin "
      "c = new; $cmp_property(c.a); end endmodule");
  EXPECT_EQ(compared, (std::vector<int>{1}));
}

}  // namespace
}  // namespace delta
