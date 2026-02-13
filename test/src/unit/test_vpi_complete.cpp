#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

// =============================================================================
// Fixture: VPI context with SimContext for integration tests
// =============================================================================

class VpiCompleteTest : public ::testing::Test {
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

// =============================================================================
// §36.8: VpiHandleC — obtain a handle by type relationship
// =============================================================================

TEST_F(VpiCompleteTest, HandleReturnsParentModule) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  vpiHandle result = VpiHandleC(vpiModule, port);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, mod);
}

TEST_F(VpiCompleteTest, HandleReturnsNullptrForNullRef) {
  vpiHandle result = VpiHandleC(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiCompleteTest, HandleReturnsNullptrForNoMatch) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  // Module has no net children, so asking for vpiNet should fail.
  vpiHandle result = VpiHandleC(vpiNet, mod);
  EXPECT_EQ(result, nullptr);
}

// =============================================================================
// §36.9: vpi_handle_by_name — name-based lookup
// =============================================================================

TEST_F(VpiCompleteTest, HandleByNameFindsModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiModule);
}

TEST_F(VpiCompleteTest, HandleByNameNullReturnsNullptr) {
  vpiHandle h = vpi_handle_by_name(nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// =============================================================================
// §36.10: VpiHandleByIndexC — index-based child lookup
// =============================================================================

TEST_F(VpiCompleteTest, HandleByIndexReturnCorrectChild) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);

  vpiHandle result = VpiHandleByIndexC(mod, 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, port_b);
}

TEST_F(VpiCompleteTest, HandleByIndexNullParentReturnsNullptr) {
  vpiHandle result = VpiHandleByIndexC(nullptr, 0);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiCompleteTest, HandleByIndexOutOfRangeReturnsNullptr) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpiHandle result = VpiHandleByIndexC(mod, 99);
  EXPECT_EQ(result, nullptr);
}

// =============================================================================
// §36.14: vpi_iterate / vpi_scan — iterator operations
// =============================================================================

TEST_F(VpiCompleteTest, IterateModuleChildPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("p0", kVpiInput, mod);
  vpi_ctx_.CreatePort("p1", kVpiOutput, mod);

  vpiHandle iter = vpi_iterate(vpiPort, mod);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiCompleteTest, IterateGlobalRegsAfterAttach) {
  sim_ctx_.CreateVariable("v1", 8);
  sim_ctx_.CreateVariable("v2", 16);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle iter = vpi_iterate(vpiReg, nullptr);
  ASSERT_NE(iter, nullptr);

  int count = 0;
  while (vpi_scan(iter) != nullptr) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST_F(VpiCompleteTest, ScanNullIteratorReturnsNull) {
  EXPECT_EQ(vpi_scan(nullptr), nullptr);
}

// =============================================================================
// §36.13: vpi_get — property access for various object types
// =============================================================================

TEST_F(VpiCompleteTest, GetTypeForModule) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  EXPECT_EQ(vpi_get(vpiType, mod), vpiModule);
}

TEST_F(VpiCompleteTest, GetTypeForPort) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  auto* port = vpi_ctx_.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiType, port), vpiPort);
}

TEST_F(VpiCompleteTest, GetTypeForParameter) {
  auto* param = vpi_ctx_.CreateParameter("WIDTH", 32);
  EXPECT_EQ(vpi_get(vpiType, param), vpiParameter);
}

TEST_F(VpiCompleteTest, GetTypeForNet) {
  auto* net_obj = vpi_ctx_.CreateNetObj("n", nullptr, 4);
  EXPECT_EQ(vpi_get(vpiType, net_obj), vpiNet);
}

TEST_F(VpiCompleteTest, GetDirectionForPort) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  auto* port = vpi_ctx_.CreatePort("din", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiDirection, port), vpiInput);
}

TEST_F(VpiCompleteTest, GetSizeForVariable) {
  auto* var = sim_ctx_.CreateVariable("wide", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("wide", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, h), 32);
}

TEST_F(VpiCompleteTest, GetReturnsZeroForNullHandle) {
  EXPECT_EQ(vpi_get(vpiType, nullptr), 0);
}

// =============================================================================
// §36.13: vpi_get_str — string property access
// =============================================================================

TEST_F(VpiCompleteTest, GetStrNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "top_mod");
}

TEST_F(VpiCompleteTest, GetStrFullNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* full = vpi_get_str(vpiFullName, h);
  ASSERT_NE(full, nullptr);
  EXPECT_STREQ(full, "lib.top_mod");
}

TEST_F(VpiCompleteTest, GetStrDefNameForModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  const char* def = vpi_get_str(vpiDefName, h);
  ASSERT_NE(def, nullptr);
  EXPECT_STREQ(def, "dut");
}

TEST_F(VpiCompleteTest, GetStrReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_str(vpiName, nullptr), nullptr);
}

// =============================================================================
// §36.18: vpi_get_value — multi-format value reading
// =============================================================================

TEST_F(VpiCompleteTest, GetValueIntFormat) {
  auto* var = sim_ctx_.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 123);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("x", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 123);
}

TEST_F(VpiCompleteTest, GetValueRealFormat) {
  auto* var = sim_ctx_.CreateVariable("r", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 42);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("r", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiRealVal;
  vpi_get_value(h, &val);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

TEST_F(VpiCompleteTest, GetValueScalarFormatZero) {
  auto* var = sim_ctx_.CreateVariable("s", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi0);
}

TEST_F(VpiCompleteTest, GetValueScalarFormatOne) {
  auto* var = sim_ctx_.CreateVariable("s1", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s1", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi1);
}

TEST_F(VpiCompleteTest, GetValueBinStrFormat) {
  auto* var = sim_ctx_.CreateVariable("b", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("b", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "1010");
}

TEST_F(VpiCompleteTest, GetValueHexStrFormat) {
  auto* var = sim_ctx_.CreateVariable("hx", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xAB);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "ab");
}

TEST_F(VpiCompleteTest, GetValueOctStrFormat) {
  auto* var = sim_ctx_.CreateVariable("oc", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 075);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("oc", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "75");
}

TEST_F(VpiCompleteTest, GetValueStringFormat) {
  auto* var = sim_ctx_.CreateVariable("sv", 32);
  // Encode "AB" as ASCII: 0x4142 = 16706
  var->value = MakeLogic4VecVal(arena_, 32, 0x00004142);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sv", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
}

TEST_F(VpiCompleteTest, GetValueTimeFormat) {
  auto* var = sim_ctx_.CreateVariable("t", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 500);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("t", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiTimeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 500);
}

// =============================================================================
// §36.19: vpi_put_value — delay modes
// =============================================================================

TEST_F(VpiCompleteTest, PutValueNoDelay) {
  auto* var = sim_ctx_.CreateVariable("d", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("d", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 77;
  vpiHandle ret = vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_NE(ret, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST_F(VpiCompleteTest, PutValueInertialDelay) {
  auto* var = sim_ctx_.CreateVariable("di", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("di", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 88;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 10;
  vpi_put_value(h, &val, &time, vpiInertialDelay);
  // For now, value is applied immediately regardless of delay mode.
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST_F(VpiCompleteTest, PutValueTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("dt", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("dt", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 99;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  vpi_put_value(h, &val, &time, vpiTransportDelay);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST_F(VpiCompleteTest, PutValuePureTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("dpt", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("dpt", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 55;
  vpi_put_value(h, &val, nullptr, vpiPureTransportDelay);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST_F(VpiCompleteTest, PutValueRealFormat) {
  auto* var = sim_ctx_.CreateVariable("rf", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rf", nullptr);
  s_vpi_value val = {};
  val.format = vpiRealVal;
  val.value.real = 7.0;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST_F(VpiCompleteTest, PutValueScalarFormat) {
  auto* var = sim_ctx_.CreateVariable("sf", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sf", nullptr);
  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
}

// =============================================================================
// §36.20: Callback registration and removal
// =============================================================================

TEST_F(VpiCompleteTest, RegisterCbReturnsHandle) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
}

TEST_F(VpiCompleteTest, RegisterCbStmt) {
  s_cb_data cb = {};
  cb.reason = cbStmt;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, cbStmt);
}

TEST_F(VpiCompleteTest, RegisterCbAtStartOfSimTime) {
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  vpiHandle h = vpi_register_cb(&cb);
  EXPECT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, cbAtStartOfSimTime);
}

TEST_F(VpiCompleteTest, RemoveCbMarksRemoved) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  int result = VpiRemoveCbC(h);
  EXPECT_EQ(result, 1);
  // After removal the callback reason is set to -1.
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, -1);
}

TEST_F(VpiCompleteTest, RemoveCbNullReturnsZero) {
  EXPECT_EQ(VpiRemoveCbC(nullptr), 0);
}

TEST_F(VpiCompleteTest, CbValueChangeWithWatcherFires) {
  auto* var = sim_ctx_.CreateVariable("sig", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sig", nullptr);
  ASSERT_NE(h, nullptr);

  bool fired = false;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = h;
  cb.user_data = &fired;
  vpi_ctx_.RegisterCbValueChange(cb);

  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->NotifyWatchers();
  EXPECT_TRUE(fired);
}

// =============================================================================
// §36.32: vpi_get_vlog_info — simulator information
// =============================================================================

TEST_F(VpiCompleteTest, GetVlogInfoReturnsProductAndVersion) {
  SVpiVlogInfo info = {};
  vpi_get_vlog_info(&info);
  ASSERT_NE(info.product, nullptr);
  ASSERT_NE(info.version, nullptr);
  EXPECT_STREQ(info.product, "DeltaHDL");
  EXPECT_STREQ(info.version, "0.1.0");
  EXPECT_EQ(info.argc, 0);
}

TEST_F(VpiCompleteTest, GetVlogInfoNullDoesNotCrash) {
  vpi_get_vlog_info(nullptr);
  // Should not crash.
}

// =============================================================================
// §36.34: VpiControlC — simulation control
// =============================================================================

TEST_F(VpiCompleteTest, ControlFinish) {
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  int result = VpiControlC(vpiFinish, 0);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.FinishRequested());
}

TEST_F(VpiCompleteTest, ControlStop) {
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  int result = VpiControlC(vpiStop, 0);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.StopRequested());
}

TEST_F(VpiCompleteTest, ControlUnknownOpReturnsZero) {
  int result = VpiControlC(999, 0);
  EXPECT_EQ(result, 0);
}

// =============================================================================
// §36.23: VpiHandleMultiC — multi-reference handle
// =============================================================================

TEST_F(VpiCompleteTest, HandleMultiCombinesChildren) {
  auto* mod1 = vpi_ctx_.CreateModule("m1", "m1");
  vpi_ctx_.CreatePort("p1", kVpiInput, mod1);

  auto* mod2 = vpi_ctx_.CreateModule("m2", "m2");
  vpi_ctx_.CreatePort("p2", kVpiOutput, mod2);

  vpiHandle h = VpiHandleMultiC(vpiPort, mod1, mod2);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(static_cast<int>(h->children.size()), 2);
}

TEST_F(VpiCompleteTest, HandleMultiBothNullReturnsNull) {
  vpiHandle h = VpiHandleMultiC(vpiPort, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// =============================================================================
// §36.33: VpiChkErrorC — error checking
// =============================================================================

TEST_F(VpiCompleteTest, ChkErrorNoErrorReturnsZero) {
  SVpiErrorInfo info = {};
  int result = VpiChkErrorC(&info);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(info.level, 0);
}

TEST_F(VpiCompleteTest, ChkErrorNullDoesNotCrash) {
  int result = VpiChkErrorC(nullptr);
  // No error pending, so returns 0.
  EXPECT_EQ(result, 0);
}

// =============================================================================
// §36.26: vpi_free_object
// =============================================================================

TEST_F(VpiCompleteTest, FreeObjectReturnsZero) {
  auto* mod = vpi_ctx_.CreateModule("tmp", "tmp");
  int result = vpi_free_object(mod);
  EXPECT_EQ(result, 0);
}

}  // namespace
}  // namespace delta
