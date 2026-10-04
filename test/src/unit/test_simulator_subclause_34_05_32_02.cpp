#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §34.5.32.2 Description, for the viewport protect pragma keyword: the access
// value is an implementation-specific relaxation of protection, and what it
// relaxes is §37.3.6's protection of an object a decryption envelope sealed.
// This tool defines two values (README.md): "r" lets a VPI application read the
// named object as it reads an unprotected one, reaching it by name through the
// protected scopes holding it, and "rw" lets it write the object's value as
// well. RecordViewportGrants in src/simulator/vpi_design_viewports.cpp gives
// the access to the object in every instance of the element declaring it, and
// VpiReadSealed and VpiWriteSealed in src/simulator/vpi_object.h are what the
// routines ask of it.

// What a PLI application reads of the sealed module's three variables while the
// design runs: one named by an "r" viewport, one by an "rw" viewport and one by
// none.
struct ViewportSeen {
  bool read_reached = false;
  int read_size = -1;
  int read_protected = -1;
  bool read_put_refused = false;
  bool read_write_reached = false;
  int read_write_value = -1;
  bool shut_reached = true;
  bool shut_refused = false;
};

ViewportSeen g_seen;

// Whether the routine called last recorded an error.
bool ErrorRecorded() {
  s_vpi_error_info info = {};
  return vpi_chk_error(&info) != 0;
}

// Writes `value` into `obj` at once.
void PutInt(vpiHandle obj, int value) {
  s_vpi_value v = {};
  v.format = vpiIntVal;
  v.value.integer = value;
  vpi_put_value(obj, &v, nullptr, vpiNoDelay);
}

PLI_INT32 ReadViewportsCalltf(PLI_BYTE8* /*user_data*/) {
  vpiHandle read = vpi_handle_by_name(VpiText("u.open_r"), nullptr);
  g_seen.read_reached = read != nullptr;
  if (read != nullptr) {
    g_seen.read_size = vpi_get(vpiSize, read);
    g_seen.read_protected = vpi_get(vpiIsProtected, read);
    PutInt(read, 3);
    g_seen.read_put_refused = ErrorRecorded();
  }
  vpiHandle read_write = vpi_handle_by_name(VpiText("u.open_rw"), nullptr);
  g_seen.read_write_reached = read_write != nullptr;
  if (read_write != nullptr) {
    PutInt(read_write, 9);
    s_vpi_value v = {};
    v.format = vpiIntVal;
    vpi_get_value(read_write, &v);
    g_seen.read_write_value = v.value.integer;
  }
  g_seen.shut_reached =
      vpi_handle_by_name(VpiText("u.shut"), nullptr) != nullptr;
  g_seen.shut_refused = ErrorRecorded();
  return 0;
}

constexpr std::string_view kKey = "viewport-exchange-key";

// A module sealed in a decryption envelope, encrypted by this tool under kKey,
// whose envelope opens two of its three variables.
std::string SealedDesignSource() {
  const std::string kAuthored =
      "`pragma protect begin\n"
      "`pragma protect viewport = (object = \"secret.open_r\", access = "
      "\"r\")\n"
      "`pragma protect viewport = (object = \"secret.open_rw\", access = "
      "\"rw\")\n"
      "module secret;\n"
      "  logic [7:0] open_r;\n"
      "  logic [7:0] open_rw;\n"
      "  logic [7:0] shut;\n"
      "endmodule\n"
      "`pragma protect end\n"
      "module t;\n"
      "  secret u();\n"
      "  initial $probe;\n"
      "endmodule\n";
  return EncryptEnvelopes(kAuthored, kKey);
}

// Registers the $probe whose calltf reads the sealed module's variables into
// g_seen.
void RegisterViewportProbe() {
  g_seen = ViewportSeen();
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadViewportsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class ViewportGrantInARun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    RegisterViewportProbe();
    RunUnderKey(SealedDesignSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

// An "r" viewport's object is reached by name through the sealed instance
// holding it.
TEST_F(ViewportGrantInARun, AReadObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_reached);
}

// Its properties are read as an unprotected object's are.
TEST_F(ViewportGrantInARun, AReadObjectsSizeIsRead) {
  EXPECT_EQ(g_seen.read_size, 8);
}

// It still represents code the envelope contained.
TEST_F(ViewportGrantInARun, AReadObjectIsStillProtected) {
  EXPECT_EQ(g_seen.read_protected, 1);
}

// "r" lets nothing write its value.
TEST_F(ViewportGrantInARun, AReadObjectRefusesAWrite) {
  EXPECT_TRUE(g_seen.read_put_refused);
}

// An "rw" viewport's object is reached too.
TEST_F(ViewportGrantInARun, AReadWriteObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_write_reached);
}

// And its value is written and read back.
TEST_F(ViewportGrantInARun, AReadWriteObjectTakesAWrite) {
  EXPECT_EQ(g_seen.read_write_value, 9);
}

// The variable no viewport names stays sealed: a name reaching it passes
// through a protected scope, which is an error.
TEST_F(ViewportGrantInARun, AnObjectNoViewportNamesIsNotReached) {
  EXPECT_FALSE(g_seen.shut_reached);
  EXPECT_TRUE(g_seen.shut_refused);
}

class ViewportGrantInABoundRun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    RegisterViewportProbe();
    RunBoundFromALibrary(SealedDesignSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

// The viewports are the envelope's whichever invocation runs the code it
// contained, so a run binding the sealed module from a library reaches an "r"
// viewport's object by name as a run compiling it does.
TEST_F(ViewportGrantInABoundRun, AReadObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_reached);
}

// And still refuses a write to it.
TEST_F(ViewportGrantInABoundRun, AReadObjectRefusesAWrite) {
  EXPECT_TRUE(g_seen.read_put_refused);
}

// An "rw" viewport's object takes a write.
TEST_F(ViewportGrantInABoundRun, AReadWriteObjectTakesAWrite) {
  EXPECT_EQ(g_seen.read_write_value, 9);
}

// And the variable no viewport names stays sealed.
TEST_F(ViewportGrantInABoundRun, AnObjectNoViewportNamesIsNotReached) {
  EXPECT_FALSE(g_seen.shut_reached);
}

}  // namespace
}  // namespace delta
