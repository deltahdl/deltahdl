#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.3.6 (Object protection properties) states that every object carries a
// vpiIsProtected Boolean property - not drawn in the data model diagrams - that
// vpi_get() reports as TRUE when the handle denotes code sealed in a decryption
// envelope and FALSE otherwise. Unless otherwise specified, accessing any
// relationship or property of a protected object is an error; the vpiType and
// vpiIsProtected properties are the stated exception and shall be permitted for
// all objects. These tests drive the production routines through the public C
// entry points, exactly as a PLI program would, by installing a private context
// as the global one.
class VpiObjectProtection : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim: every object has a vpiIsProtected property and vpi_get() reports it as
// a Boolean - FALSE for an ordinary object that holds no protected code.
TEST_F(VpiObjectProtection, GetIsProtectedReportsFalseForOrdinaryObject) {
  VpiObject net;
  net.type = vpiNet;
  // default-constructed objects are not protected
  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(&net)), 0);
}

// Claim: access to the vpiType property of a protected object shall be
// permitted for all objects - vpi_get(vpiType, ...) returns the real type
// constant rather than erroring, and leaves no error recorded.
TEST_F(VpiObjectProtection, GetTypeIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&mod)), vpiModule);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// Claim: access to the vpiIsProtected property of a protected object is
// likewise permitted - it is not blocked by the protected-object guard and
// reports TRUE without recording an error.
TEST_F(VpiObjectProtection, GetIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(&mod)), 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// Claim: unless otherwise specified, access to a property of a protected object
// is an error. Any property other than the two permitted exceptions records an
// error and yields vpiUndefined, the value vpi_get() returns on an error.
TEST_F(VpiObjectProtection, GetOtherPropertyOnProtectedObjectIsAnError) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 32;
  reg.is_protected = true;

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&reg)), vpiUndefined);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

// Claim (string form of the permitted exception): vpiType remains accessible on
// a protected object through vpi_get_str, which hands back the type-constant
// name without recording an error.
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

// Claim (string form of the general rule): a string query for any other
// property of a protected object is an error - it records the error and
// supplies no string (a null pointer).
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

// Claim (string form of the second permitted exception): vpiIsProtected is,
// like vpiType, permitted on a protected object for all objects. Through
// vpi_get_str it has no string representation (it is a Boolean), so the call
// hands back a null pointer - but the protected-object guard must not have
// fired, so no error is recorded. This distinguishes the permitted exception
// (silent null) from a blocked property (null plus a recorded error).
TEST_F(VpiObjectProtection, GetStrIsProtectedIsPermittedOnProtectedObject) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiIsProtected, VpiHandleOf(&mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// Claim (relationship half of the general rule): the protected-object guard
// covers access to an object's *relationships*, not only its properties -
// "access to relationships and properties of a protected object shall be an
// error." Traversing a one-to-one relationship out of a protected reference
// object records an error and yields no handle, whereas the identical traversal
// from an ordinary object resolves normally. This confirms the guard keys off
// the reference object's protection state rather than the traversal itself.
TEST_F(VpiObjectProtection, RelationshipAccessOnProtectedObjectIsAnError) {
  VpiObject child;
  child.type = vpiNet;

  VpiObject open_mod;
  open_mod.type = vpiModule;
  open_mod.children.push_back(&child);
  // The contained-net relationship resolves from an unprotected reference.
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNet, VpiHandleOf(&open_mod))), &child);
  s_vpi_error_info ok = {};
  EXPECT_EQ(vpi_chk_error(&ok), 0);

  VpiObject locked_mod;
  locked_mod.type = vpiModule;
  locked_mod.children.push_back(&child);
  locked_mod.is_protected = true;
  // ...but the same traversal is refused once the reference is protected.
  EXPECT_EQ(vpi_handle(vpiNet, VpiHandleOf(&locked_mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

// Edge (boundary of the protected-object rule): the access error applies only
// to protected objects. An ordinary object reports a non-exception property
// such as vpiSize normally and records no error, confirming the guard keys off
// the object's protection state rather than the property being requested.
TEST_F(VpiObjectProtection, GetNonExceptionPropertyOnOrdinaryObjectSucceeds) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 16;
  // not protected

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&reg)), 16);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// What a PLI application reads of the design below while it runs: whether the
// instance of the sealed module, the instance of the cleartext one and a net
// declared inside the sealed module are protected, whether the sealed
// instance's type and nets can be read, and whether the cleartext one's nets
// can.
struct ProtectionSeen {
  int sealed_protected = -1;
  int sealed_type = -1;
  bool sealed_nets_reached = true;
  int inner_net_protected = -1;
  int clear_protected = -1;
  bool clear_nets_reached = false;
};

ProtectionSeen g_seen;

// The net named `name` among the children of `scope`, read off the object
// itself, which no VPI routine reaches inside a protected scope.
VpiObject* NetNamedIn(vpiHandle scope, std::string_view name) {
  if (scope == nullptr) return nullptr;
  for (VpiObject* child : VpiObjectOf(scope)->children) {
    if (child->name == name) return child;
  }
  return nullptr;
}

PLI_INT32 ReadProtectionCalltf(PLI_BYTE8* /*user_data*/) {
  vpiHandle sealed = vpi_handle_by_name(VpiText("u"), nullptr);
  if (sealed != nullptr) {
    g_seen.sealed_protected = vpi_get(vpiIsProtected, sealed);
    g_seen.sealed_type = vpi_get(vpiType, sealed);
    g_seen.sealed_nets_reached = vpi_iterate(vpiNet, sealed) != nullptr;
    VpiObject* inner = NetNamedIn(sealed, "inner");
    if (inner != nullptr) g_seen.inner_net_protected = inner->is_protected;
  }
  vpiHandle clear = vpi_handle_by_name(VpiText("c"), nullptr);
  if (clear != nullptr) {
    g_seen.clear_protected = vpi_get(vpiIsProtected, clear);
    vpiHandle nets = vpi_iterate(vpiNet, clear);
    g_seen.clear_nets_reached = nets != nullptr;
    if (nets != nullptr) vpi_free_object(nets);
  }
  return 0;
}

constexpr std::string_view kKey = "protection-exchange-key";

// A design instantiating a module sealed in a decryption envelope and one
// written in the clear, encrypted by this tool under kKey.
std::string SealedDesignSource() {
  const std::string kAuthored =
      "`pragma protect begin\n"
      "module secret(input a, output y);\n"
      "  wire inner;\n"
      "  assign y = a;\n"
      "endmodule\n"
      "`pragma protect end\n"
      "module clear(input a);\n"
      "  wire seen;\n"
      "endmodule\n"
      "module t;\n"
      "  wire a, y;\n"
      "  secret u(.a(a), .y(y));\n"
      "  clear c(.a(a));\n"
      "  initial $probe;\n"
      "endmodule\n";
  return EncryptEnvelopes(kAuthored, kKey);
}

// The sealed design read back as a compile reads it: preprocessed under the
// exchange key, its text registered with the origin of each line, elaborated
// from the top and run.
void RunADesignWithASealedModule(SimFixture& f) {
  PreprocConfig config;
  config.protect_key = std::string(kKey);
  Preprocessor pp(f.mgr, f.diag, config);
  std::string text =
      pp.Preprocess(f.mgr.AddFile("<test>", SealedDesignSource()));
  uint32_t fid = f.mgr.AddPreprocessedFile("<test>", text, pp.LineOrigins());
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  Elaborator elab(f.arena, f.diag, parser.Parse());
  RtlirDesign* design = elab.Elaborate("t");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
}

// The sealed design compiled into a library by one invocation (§33.5.3) and
// bound and run by another (§33.5.4), which reads the library's compiled form
// and never the source.
void RunTheSealedDesignBoundFromALibrary(SimFixture& f) {
  ScratchDir tmp;
  const std::string kSource = (tmp.dir / "sealed.sv").string();
  std::ofstream(kSource) << SealedDesignSource();
  CliOptions opts;
  opts.source_files = {kSource};
  opts.precompile_library = "ip";
  opts.precompile_output = (tmp.dir / "ip.dpl").string();
  opts.protect.exchange_key = std::string(kKey);
  SourceManager precompile_mgr;
  DiagEngine precompile_diag{precompile_mgr};
  ASSERT_EQ(RunPrecompile(opts, precompile_mgr, precompile_diag), 0);
  SeparateCompilationBinder binder(f.mgr, f.arena, f.diag);
  ASSERT_TRUE(binder.LoadLibrary(opts.precompile_output));
  RtlirDesign* design = binder.Bind({"t"});
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
}

// Registers the $probe whose calltf reads the design's protection into g_seen.
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
    RunADesignWithASealedModule(f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

// §37.3.6: the instance of a module declared in a decryption envelope
// represents code contained in it, so it reports vpiIsProtected TRUE.
TEST_F(VpiProtectionInARun, AnInstanceOfASealedModuleIsProtected) {
  EXPECT_EQ(g_seen.sealed_protected, 1);
}

// Its vpiType stays readable, as it does for every object.
TEST_F(VpiProtectionInARun, ItsTypeStaysReadable) {
  EXPECT_EQ(g_seen.sealed_type, vpiModule);
}

// The nets it contains are not reached through it, that being a relationship
// of a protected object.
TEST_F(VpiProtectionInARun, ItsNetsAreNotReached) {
  EXPECT_FALSE(g_seen.sealed_nets_reached);
}

// A net declared inside the sealed module is itself code the envelope
// contained.
TEST_F(VpiProtectionInARun, ANetDeclaredInsideItIsProtected) {
  EXPECT_EQ(g_seen.inner_net_protected, 1);
}

// The instance of a module written in the clear is not protected.
TEST_F(VpiProtectionInARun, AnInstanceOfACleartextModuleIsNot) {
  EXPECT_EQ(g_seen.clear_protected, 0);
}

// And its nets are reached as ever.
TEST_F(VpiProtectionInARun, ACleartextInstancesNetsAreReached) {
  EXPECT_TRUE(g_seen.clear_nets_reached);
}

class VpiProtectionInABoundRun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    RegisterProtectionProbe();
    RunTheSealedDesignBoundFromALibrary(f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

// §37.3.6: the code is the code the envelope contained whichever invocation
// runs it, so the instance of the sealed module is protected in a run that
// binds it from a library as in one that compiles it.
TEST_F(VpiProtectionInABoundRun, AnInstanceOfASealedModuleIsProtected) {
  EXPECT_EQ(g_seen.sealed_protected, 1);
}

// And the net declared inside it.
TEST_F(VpiProtectionInABoundRun, ANetDeclaredInsideItIsProtected) {
  EXPECT_EQ(g_seen.inner_net_protected, 1);
}

// The library holds the cleartext module beside it, and its instance is not.
TEST_F(VpiProtectionInABoundRun, AnInstanceOfACleartextModuleIsNot) {
  EXPECT_EQ(g_seen.clear_protected, 0);
}

// A variable the design holds, its VPI object marked protected as one
// declared in a decryption envelope is, for the value routines to be asked of.
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

  // The message of the error the last routine recorded, empty for none.
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

// §37.3.6: a protected object's value is not read: vpi_get_value records an
// error and leaves the caller's value as it was.
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

// §37.3.6: nor is it written: vpi_put_value records an error, changes nothing
// and schedules no event.
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

// The array forms refuse a protected object the same way.
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

// An object no envelope sealed is read as ever, with no error.
TEST_F(VpiProtectedValueAccess, AnUnprotectedObjectIsRead) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(handle_, &value);
  EXPECT_EQ(value.value.integer, 5);
}

}  // namespace
}  // namespace delta
