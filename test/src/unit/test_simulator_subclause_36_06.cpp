#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_seen = 0;

PLI_INT32 ReadRCalltf(PLI_BYTE8*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText("r"), nullptr), &val);
  g_seen = val.value.integer;
  return 0;
}

PLI_INT32 WriteRCalltf(PLI_BYTE8*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 42;
  vpi_put_value(vpi_handle_by_name(VpiText("r"), nullptr), &val, nullptr,
                vpiNoDelay);
  return 0;
}

void RegisterProbe(PLI_INT32 (*calltf)(PLI_BYTE8*)) {
  g_seen = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = calltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class PliApplicationDesignAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PliApplicationDesignAccess, TheApplicationReadsTheDesignAsItRuns) {
  RegisterProbe(&ReadRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = 7;\n"
      "    $probe;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_seen, 7);
}

TEST_F(PliApplicationDesignAccess, TheApplicationWritesWhereTheDesignReads) {
  RegisterProbe(&WriteRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  int after;\n"
      "  initial begin\n"
      "    r = 1;\n"
      "    $probe;\n"
      "    after = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* after = f.ctx.FindVariable("after");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->value.ToUint64(), 42u);
}

PLI_INT32 ReadThenWriteRCalltf(PLI_BYTE8* user_data) {
  ReadRCalltf(user_data);
  WriteRCalltf(user_data);
  return 0;
}

PLI_INT32 ReadWriteAndReturnCalltf(PLI_BYTE8* user_data) {
  ReadThenWriteRCalltf(user_data);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = g_seen + 1;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &val, nullptr, vpiNoDelay);
  return 0;
}

uint64_t AfterOf(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return ~uint64_t{0};
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* after = f.ctx.FindVariable("after");
  return after == nullptr ? ~uint64_t{0} : after->value.ToUint64();
}

void ExpectTheProbeReadsSevenAndWritesFortyTwo(const std::string& src) {
  RegisterProbe(&ReadThenWriteRCalltf);
  EXPECT_EQ(AfterOf(src), 42U);
  EXPECT_EQ(g_seen, 7);
}

TEST_F(PliApplicationDesignAccess,
       ASystemFunctionInAnExpressionReadsAndWrites) {
  g_seen = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$pf");
  data.calltf = ReadWriteAndReturnCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  EXPECT_EQ(AfterOf("module t;\n"
                    "  int r, after;\n"
                    "  initial begin\n"
                    "    r = 7;\n"
                    "    after = $pf() * 100;\n"
                    "    after = after + r;\n"
                    "  end\n"
                    "endmodule\n"),
            842U);
  EXPECT_EQ(g_seen, 7);
}

TEST_F(PliApplicationDesignAccess, ACallInATaskBodyReadsAndWrites) {
  ExpectTheProbeReadsSevenAndWritesFortyTwo(
      "module t;\n"
      "  int r, after;\n"
      "  task k(); $probe; endtask\n"
      "  initial begin r = 7; k(); after = r; end\n"
      "endmodule\n");
}

TEST_F(PliApplicationDesignAccess, ACallInAFunctionBodyReadsAndWrites) {
  ExpectTheProbeReadsSevenAndWritesFortyTwo(
      "module t;\n"
      "  int r, after;\n"
      "  function void g(); $probe; endfunction\n"
      "  initial begin r = 7; g(); after = r; end\n"
      "endmodule\n");
}

TEST_F(PliApplicationDesignAccess, ACallInAClassMethodReadsAndWrites) {
  ExpectTheProbeReadsSevenAndWritesFortyTwo(
      "module t;\n"
      "  int r, after;\n"
      "  class C; function void k(); $probe; endfunction endclass\n"
      "  C o;\n"
      "  initial begin o = new; r = 7; o.k(); after = r; end\n"
      "endmodule\n");
}

TEST_F(PliApplicationDesignAccess, ACallInAProgramReadsAndWrites) {
  ExpectTheProbeReadsSevenAndWritesFortyTwo(
      "program t;\n"
      "  int r, after;\n"
      "  initial begin r = 7; $probe; after = r; end\n"
      "endprogram\n");
}

int g_compiles = 0;

PLI_INT32 CountCompile(PLI_BYTE8*) {
  ++g_compiles;
  return 0;
}

TEST_F(PliApplicationDesignAccess, ANameThatIsCompiledButNeverRunIsCompiled) {
  g_compiles = 0;
  RegisterProbe(&ReadRCalltf);
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$unrun");
  data.compiletf = CountCompile;
  data.calltf = ReadThenWriteRCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  EXPECT_EQ(AfterOf("module t;\n"
                    "  int r, after;\n"
                    "  initial begin r = 7; if (r == 0) $unrun; after = r; "
                    "end\n"
                    "endmodule\n"),
            7U);
  EXPECT_EQ(g_compiles, 1);
  EXPECT_EQ(g_seen, 0);
}

}  // namespace
}  // namespace delta
