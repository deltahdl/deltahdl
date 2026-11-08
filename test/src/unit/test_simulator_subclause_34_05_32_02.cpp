#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/envelope_viewport.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_sealed_design_run.h"
#include "parser/ast_design.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

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

bool ErrorRecorded() {
  s_vpi_error_info info = {};
  return vpi_chk_error(&info) != 0;
}

void PutInt(vpiHandle obj, int value) {
  s_vpi_value v = {};
  v.format = vpiIntVal;
  v.value.integer = value;
  vpi_put_value(obj, &v, nullptr, vpiNoDelay);
}

PLI_INT32 ReadViewportsCalltf(PLI_BYTE8*) {
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

TEST_F(ViewportGrantInARun, AReadObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_reached);
}

TEST_F(ViewportGrantInARun, AReadObjectsSizeIsRead) {
  EXPECT_EQ(g_seen.read_size, 8);
}

TEST_F(ViewportGrantInARun, AReadObjectIsStillProtected) {
  EXPECT_EQ(g_seen.read_protected, 1);
}

TEST_F(ViewportGrantInARun, AReadObjectRefusesAWrite) {
  EXPECT_TRUE(g_seen.read_put_refused);
}

TEST_F(ViewportGrantInARun, AReadWriteObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_write_reached);
}

TEST_F(ViewportGrantInARun, AReadWriteObjectTakesAWrite) {
  EXPECT_EQ(g_seen.read_write_value, 9);
}

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

TEST_F(ViewportGrantInABoundRun, AReadObjectIsReachedByName) {
  EXPECT_TRUE(g_seen.read_reached);
}

TEST_F(ViewportGrantInABoundRun, AReadObjectRefusesAWrite) {
  EXPECT_TRUE(g_seen.read_put_refused);
}

TEST_F(ViewportGrantInABoundRun, AReadWriteObjectTakesAWrite) {
  EXPECT_EQ(g_seen.read_write_value, 9);
}

TEST_F(ViewportGrantInABoundRun, AnObjectNoViewportNamesIsNotReached) {
  EXPECT_FALSE(g_seen.shut_reached);
}

struct PartialGrantSeen {
  bool undefined_reached = true;
  bool generated_reached = false;
};

PartialGrantSeen g_partial;

PLI_INT32 ReadPartialGrantsCalltf(PLI_BYTE8*) {
  g_partial.undefined_reached =
      vpi_handle_by_name(VpiText("u1.undefined"), nullptr) != nullptr;
  g_partial.generated_reached =
      vpi_handle_by_name(VpiText("u1.g.q"), nullptr) != nullptr;
  return 0;
}

std::string PartiallyGrantedSource() {
  const std::string kAuthored =
      "`pragma protect begin\n"
      "`pragma protect viewport = (object = \"secret.undefined\", access = "
      "\"x\")\n"
      "`pragma protect viewport = (object = \"secret.g.q\", access = \"r\")\n"
      "module secret #(parameter P = 0);\n"
      "  logic [7:0] undefined;\n"
      "  if (P) begin : g\n"
      "    logic [7:0] q;\n"
      "  end\n"
      "endmodule\n"
      "`pragma protect end\n"
      "module t;\n"
      "  secret #(.P(0)) u0();\n"
      "  secret #(.P(1)) u1();\n"
      "  initial $probe;\n"
      "endmodule\n";
  return EncryptEnvelopes(kAuthored, kKey);
}

class PartialViewportGrantInARun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_partial = PartialGrantSeen();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ReadPartialGrantsCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    RunUnderKey(PartiallyGrantedSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(PartialViewportGrantInARun, AnUndefinedAccessLeavesItsObjectSealed) {
  EXPECT_FALSE(g_partial.undefined_reached);
}

TEST_F(PartialViewportGrantInARun, AnInstanceThatGeneratedTheObjectIsGranted) {
  EXPECT_TRUE(g_partial.generated_reached);
}

TEST(ViewportGrantOutsideARun, AViewportNamingNothingGrantsNothing) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  SimFixture f;
  EnvelopeViewport viewport;
  viewport.object = "absent.q";
  viewport.access = std::string(kViewportReadAccess);
  f.mgr.AddViewport(viewport);
  CompilationUnit unit;
  RtlirModule top;
  top.name = "t";
  RtlirDesign design;
  design.compilation_unit = &unit;
  design.top_modules = {&top};
  vpi_ctx.Attach(f.ctx, &design);
  EXPECT_EQ(vpi_handle_by_name(VpiText("absent.q"), nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
