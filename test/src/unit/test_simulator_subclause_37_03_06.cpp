#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"
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

// A design instantiating a module sealed in a decryption envelope and one
// written in the clear, encrypted by this tool and read back as a compile
// reads it: preprocessed under the exchange key, its text registered with
// the origin of each line, elaborated from the top and run.
void RunADesignWithASealedModule(SimFixture& f) {
  constexpr std::string_view kKey = "protection-exchange-key";
  std::string authored =
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
  PreprocConfig config;
  config.protect_key = std::string(kKey);
  Preprocessor pp(f.mgr, f.diag, config);
  std::string text =
      pp.Preprocess(f.mgr.AddFile("<test>", EncryptEnvelopes(authored, kKey)));
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

class VpiProtectionInARun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_seen = ProtectionSeen();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ReadProtectionCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
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
}  // namespace
}  // namespace delta
