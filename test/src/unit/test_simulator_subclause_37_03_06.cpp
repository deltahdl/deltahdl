#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiObjectProtection : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(VpiObjectProtection, GetIsProtectedReportsFalseForOrdinaryObject) {
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(&net)), 0);
}

TEST_F(VpiObjectProtection, GetTypeIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&mod)), vpiModule);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST_F(VpiObjectProtection, GetIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(&mod)), 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST_F(VpiObjectProtection, GetOtherPropertyOnProtectedObjectIsAnError) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.line_no = 7;
  reg.is_protected = true;

  EXPECT_EQ(vpi_get(vpiLineNo, VpiHandleOf(&reg)), vpiUndefined);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

TEST_F(VpiObjectProtection, GetStrTypeIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  const char* type_name = vpi_get_str(vpiType, VpiHandleOf(&mod));
  ASSERT_NE(type_name, nullptr);
  EXPECT_EQ(std::string(type_name), "vpiModule");

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST_F(VpiObjectProtection, GetStrOtherPropertyOnProtectedObjectIsAnError) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "locked";
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

TEST_F(VpiObjectProtection, GetStrIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiIsProtected, VpiHandleOf(&mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST_F(VpiObjectProtection, RelationshipAccessOnProtectedObjectIsAnError) {
  VpiObject child;
  child.type = vpiNet;

  VpiObject open_mod;
  open_mod.type = vpiModule;
  open_mod.children.push_back(&child);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNet, VpiHandleOf(&open_mod))), &child);
  s_vpi_error_info ok = {};
  EXPECT_EQ(vpi_chk_error(&ok), 0);

  VpiObject locked_mod;
  locked_mod.type = vpiModule;
  locked_mod.children.push_back(&child);
  locked_mod.is_protected = true;
  EXPECT_EQ(vpi_handle(vpiNet, VpiHandleOf(&locked_mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

TEST_F(VpiObjectProtection, IterationOnProtectedObjectIsAnError) {
  VpiObject child;
  child.type = vpiNet;

  VpiObject open_mod;
  open_mod.type = vpiModule;
  open_mod.children.push_back(&child);
  vpiHandle nets = vpi_iterate(vpiNet, VpiHandleOf(&open_mod));
  EXPECT_NE(nets, nullptr);
  s_vpi_error_info ok = {};
  EXPECT_EQ(vpi_chk_error(&ok), 0);
  vpi_free_object(nets);

  VpiObject locked_mod;
  locked_mod.type = vpiModule;
  locked_mod.children.push_back(&child);
  locked_mod.is_protected = true;
  EXPECT_EQ(vpi_iterate(vpiNet, VpiHandleOf(&locked_mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_EQ(info.level, vpiError);
  ASSERT_NE(info.message, nullptr);
  EXPECT_NE(std::string(info.message).find("protected"), std::string::npos);
}

TEST_F(VpiObjectProtection, GetNonExceptionPropertyOnOrdinaryObjectSucceeds) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 16;

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&reg)), 16);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

struct WrittenItemsSeen {
  int cont_assign = -1;
  int process = -1;
  int block = -1;
  int assertion = -1;
};

struct ProtectionSeen {
  int sealed_protected = -1;
  int sealed_type = -1;
  bool sealed_nets_reached = true;
  int inner_net_protected = -1;
  int clear_protected = -1;
  bool clear_nets_reached = false;
  WrittenItemsSeen sealed_items;
  WrittenItemsSeen clear_items;
};

ProtectionSeen g_seen;

VpiObject* NetNamedIn(vpiHandle scope, std::string_view name) {
  if (scope == nullptr) return nullptr;
  for (VpiObject* child : VpiObjectOf(scope)->children) {
    if (child->name == name) return child;
  }
  return nullptr;
}

VpiObject* ChildOfType(VpiObject* obj, int type) {
  if (obj == nullptr) return nullptr;
  for (VpiObject* child : obj->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

int ProtectionOf(VpiObject* obj) {
  return obj == nullptr ? -1 : vpi_get(vpiIsProtected, VpiHandleOf(obj));
}

WrittenItemsSeen ReadWrittenItems(vpiHandle scope) {
  VpiObject* instance = VpiObjectOf(scope);
  VpiObject* process = ChildOfType(instance, vpiInitial);
  return {ProtectionOf(ChildOfType(instance, vpiContAssign)),
          ProtectionOf(process),
          ProtectionOf(process == nullptr ? nullptr : process->body),
          ProtectionOf(ChildOfType(instance, vpiAssert))};
}

PLI_INT32 ReadProtectionCalltf(PLI_BYTE8*) {
  vpiHandle sealed = vpi_handle_by_name(VpiText("u"), nullptr);
  if (sealed != nullptr) {
    g_seen.sealed_protected = vpi_get(vpiIsProtected, sealed);
    g_seen.sealed_type = vpi_get(vpiType, sealed);
    g_seen.sealed_nets_reached = vpi_iterate(vpiNet, sealed) != nullptr;
    VpiObject* inner = NetNamedIn(sealed, "inner");
    if (inner != nullptr) g_seen.inner_net_protected = inner->is_protected;
    g_seen.sealed_items = ReadWrittenItems(sealed);
  }
  vpiHandle clear = vpi_handle_by_name(VpiText("c"), nullptr);
  if (clear != nullptr) {
    g_seen.clear_protected = vpi_get(vpiIsProtected, clear);
    vpiHandle nets = vpi_iterate(vpiNet, clear);
    g_seen.clear_nets_reached = nets != nullptr;
    if (nets != nullptr) vpi_free_object(nets);
    g_seen.clear_items = ReadWrittenItems(clear);
  }
  return 0;
}

constexpr std::string_view kKey = "protection-exchange-key";

std::string SealedDesignSource() {
  const std::string kAuthored =
      "`pragma protect begin\n"
      "module secret(input a, output y);\n"
      "  wire inner;\n"
      "  assign y = a;\n"
      "  initial begin end\n"
      "  a1: assert property (@(posedge a) a);\n"
      "endmodule\n"
      "`pragma protect end\n"
      "module clear(input a);\n"
      "  wire seen, z;\n"
      "  assign z = a;\n"
      "  initial begin end\n"
      "  a1: assert property (@(posedge a) a);\n"
      "endmodule\n"
      "module t;\n"
      "  wire a, y;\n"
      "  secret u(.a(a), .y(y));\n"
      "  clear c(.a(a));\n"
      "  initial $probe;\n"
      "endmodule\n";
  return EncryptEnvelopes(kAuthored, kKey);
}

void RegisterProtectionProbe() {
  g_seen = ProtectionSeen();
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadProtectionCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class VpiProtectionInARun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    RegisterProtectionProbe();
    RunUnderKey(SealedDesignSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(VpiProtectionInARun, AnInstanceOfASealedModuleIsProtected) {
  EXPECT_EQ(g_seen.sealed_protected, 1);
}

TEST_F(VpiProtectionInARun, ItsTypeStaysReadable) {
  EXPECT_EQ(g_seen.sealed_type, vpiModule);
}

TEST_F(VpiProtectionInARun, ItsNetsAreNotReached) {
  EXPECT_FALSE(g_seen.sealed_nets_reached);
}

TEST_F(VpiProtectionInARun, ANetDeclaredInsideItIsProtected) {
  EXPECT_EQ(g_seen.inner_net_protected, 1);
}

TEST_F(VpiProtectionInARun, AnInstanceOfACleartextModuleIsNot) {
  EXPECT_EQ(g_seen.clear_protected, 0);
}

TEST_F(VpiProtectionInARun, ACleartextInstancesNetsAreReached) {
  EXPECT_TRUE(g_seen.clear_nets_reached);
}

TEST_F(VpiProtectionInARun, TheItemsWrittenInsideItAreProtected) {
  EXPECT_EQ(g_seen.sealed_items.cont_assign, 1);
  EXPECT_EQ(g_seen.sealed_items.process, 1);
  EXPECT_EQ(g_seen.sealed_items.block, 1);
  EXPECT_EQ(g_seen.sealed_items.assertion, 1);
}

TEST_F(VpiProtectionInARun, TheItemsWrittenInTheClearAreNot) {
  EXPECT_EQ(g_seen.clear_items.cont_assign, 0);
  EXPECT_EQ(g_seen.clear_items.process, 0);
  EXPECT_EQ(g_seen.clear_items.block, 0);
  EXPECT_EQ(g_seen.clear_items.assertion, 0);
}

class VpiProtectionInABoundRun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    RegisterProtectionProbe();
    RunBoundFromALibrary(SealedDesignSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(VpiProtectionInABoundRun, AnInstanceOfASealedModuleIsProtected) {
  EXPECT_EQ(g_seen.sealed_protected, 1);
}

TEST_F(VpiProtectionInABoundRun, ANetDeclaredInsideItIsProtected) {
  EXPECT_EQ(g_seen.inner_net_protected, 1);
}

TEST_F(VpiProtectionInABoundRun, AnInstanceOfACleartextModuleIsNot) {
  EXPECT_EQ(g_seen.clear_protected, 0);
}

class VpiProtectedValueAccess : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_);
    var_ = sim_.CreateVariable("sealed_v", 32);
    var_->value = MakeLogic4VecVal(arena_, 32, 5);
    vpi_.Attach(sim_);
    handle_ = vpi_handle_by_name(VpiText("sealed_v"), nullptr);
    ASSERT_NE(handle_, nullptr);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void Protect() { VpiObjectOf(handle_)->is_protected = true; }

  std::string LastError() {
    s_vpi_error_info info = {};
    if (vpi_chk_error(&info) == 0 || info.message == nullptr) return "";
    return info.message;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_{scheduler_, arena_, diag_};
  VpiContext vpi_;
  Variable* var_ = nullptr;
  vpiHandle handle_ = nullptr;
};

TEST_F(VpiProtectedValueAccess, GetValueLeavesTheCallersValue) {
  Protect();
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 99;
  vpi_get_value(handle_, &value);
  EXPECT_EQ(value.value.integer, 99);
}

TEST_F(VpiProtectedValueAccess, GetValueIsAnError) {
  Protect();
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(handle_, &value);
  EXPECT_NE(LastError().find("protected"), std::string::npos);
}

TEST_F(VpiProtectedValueAccess, PutValueChangesNothing) {
  Protect();
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 77;
  EXPECT_EQ(vpi_put_value(handle_, &value, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(var_->value.ToUint64(), 5U);
}

TEST_F(VpiProtectedValueAccess, PutValueIsAnError) {
  Protect();
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 77;
  vpi_put_value(handle_, &value, nullptr, vpiNoDelay);
  EXPECT_NE(LastError().find("protected"), std::string::npos);
}

TEST_F(VpiProtectedValueAccess, GetValueArrayIsAnError) {
  Protect();
  s_vpi_arrayvalue values = {};
  values.format = vpiIntVal;
  int index = 0;
  vpi_get_value_array(handle_, &values, &index, 1);
  EXPECT_NE(LastError().find("protected"), std::string::npos);
}

TEST_F(VpiProtectedValueAccess, PutValueArrayIsAnError) {
  Protect();
  s_vpi_arrayvalue values = {};
  values.format = vpiIntVal;
  int index = 0;
  vpi_put_value_array(handle_, &values, &index, 1);
  EXPECT_NE(LastError().find("protected"), std::string::npos);
}

TEST_F(VpiProtectedValueAccess, AnUnprotectedObjectIsRead) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(handle_, &value);
  EXPECT_EQ(value.value.integer, 5);
}

}  // namespace
}  // namespace delta
