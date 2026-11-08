#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
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

class VpiIterateSim : public ::testing::Test {
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

TEST_F(VpiIterateSim, IterateModuleChildPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiIterateSim, IterateRegsOfAScopeAfterAttach) {
  sim_ctx_.CreateVariable("m1.v1", 8);
  sim_ctx_.CreateVariable("m1.v2", 16);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  ASSERT_NE(mod, nullptr);

  vpiHandle iter = vpi_iterate(vpiReg, mod);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiIterateSim, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

TEST_F(VpiIterateSim, IteratorHandleTypeIsIterator) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);
}

TEST_F(VpiIterateSim, HandleVpiUseReturnsReferenceObject) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(mod));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUse, iter)), mod);
}

TEST_F(VpiIterateSim, IterateProtectedObjectReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  mod->is_protected = true;

  EXPECT_EQ(vpi_iterate(vpiPort, VpiHandleOf(mod)), nullptr);
}

TEST_F(VpiIterateSim, IterateNoMatchingObjectsReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);

  EXPECT_EQ(vpi_iterate(vpiParameter, VpiHandleOf(mod)), nullptr);
}

int g_nets_seen = 0;
std::string g_first_net_name;
std::string g_second_net_name;
int g_widest_net_size = 0;

PLI_INT32 DisplayNetsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiNet, mod);
  if (itr == nullptr) return 0;
  for (vpiHandle net = vpi_scan(itr); net != nullptr; net = vpi_scan(itr)) {
    ++g_nets_seen;
    const char* name = vpi_get_str(vpiName, net);
    if (name != nullptr) {
      (g_nets_seen == 1 ? g_first_net_name : g_second_net_name) = name;
    }
    int size = vpi_get(vpiSize, net);
    if (size > g_widest_net_size) g_widest_net_size = size;
  }
  return 0;
}

void RegisterNetProbe() {
  g_nets_seen = 0;
  g_first_net_name.clear();
  g_second_net_name.clear();
  g_widest_net_size = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &DisplayNetsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunAModuleOfTwoNets(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class VpiIterateInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiIterateInARun, TheIterationWalksEveryNetTheModuleDeclares) {
  RegisterNetProbe();

  SimFixture f;
  RunAModuleOfTwoNets(f);

  EXPECT_EQ(g_nets_seen, 2);
  EXPECT_TRUE(g_first_net_name == "w" || g_second_net_name == "w");
  EXPECT_TRUE(g_first_net_name == "bus" || g_second_net_name == "bus");
}

TEST_F(VpiIterateInARun, TheExamplesVectorNetReportsItsSize) {
  RegisterNetProbe();

  SimFixture f;
  RunAModuleOfTwoNets(f);

  EXPECT_EQ(g_widest_net_size, 8);
}

TEST(VpiIterateRelations, AnUnnamedRelationWalksChildrenOfItsType) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  for (int kind : {vpiLetExpr, vpiInterconnectArray, vpiExtends, vpiTchk,
                   vpiForeachStmt, vpiFor, vpiModPath, vpiCaseItem}) {
    VpiObject event;
    event.type = vpiNamedEvent;
    VpiObject ref;
    ref.type = kind;
    ref.children = {&event};
    vpiHandle it = vpi_iterate(vpiNamedEvent, VpiHandleOf(&ref));
    ASSERT_NE(it, nullptr) << kind;
    EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &event) << kind;
    EXPECT_EQ(vpi_scan(it), nullptr) << kind;
  }
  SetGlobalVpiContext(nullptr);
}

TEST(VpiIterateRelations, AGateArrayElementHasNoIndexIteration) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject index;
  index.type = vpiConstant;
  VpiObject gate;
  gate.type = vpiGate;
  gate.array_member = true;
  gate.children = {&index};
  EXPECT_EQ(vpi_iterate(vpiIndex, VpiHandleOf(&gate)), nullptr);
  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
