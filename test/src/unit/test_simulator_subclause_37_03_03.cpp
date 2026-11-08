#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiFileAndLineProperty : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(VpiFileAndLineProperty, GetLineNoReturnsTheObjectsSourceLine) {
  VpiObject net;
  net.type = vpiNet;
  net.line_no = 42;

  EXPECT_EQ(vpi_get(vpiLineNo, VpiHandleOf(&net)), 42);
}

TEST_F(VpiFileAndLineProperty, GetStrFileReturnsTheObjectsSourceFile) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.file = "design.sv";

  const char* file = vpi_get_str(vpiFile, VpiHandleOf(&reg));
  ASSERT_NE(file, nullptr);
  EXPECT_EQ(std::string(file), "design.sv");
}

TEST_F(VpiFileAndLineProperty, ExceptedKindsHaveNoLineNo) {
  const int kExcepted[] = {vpiCallback,      vpiDelayTerm, vpiDelayDevice,
                           vpiInterModPath,  vpiIterator,  vpiTimeQueue,
                           vpiGenScopeArray, vpiGenScope};
  for (int type : kExcepted) {
    VpiObject obj;
    obj.type = type;
    obj.line_no = 99;
    EXPECT_EQ(vpi_get(vpiLineNo, VpiHandleOf(&obj)), vpiUndefined)
        << "object type " << type << " must not report a vpiLineNo";
  }
}

TEST_F(VpiFileAndLineProperty, ExceptedKindsHaveNoFile) {
  const int kExcepted[] = {vpiCallback,      vpiDelayTerm, vpiDelayDevice,
                           vpiInterModPath,  vpiIterator,  vpiTimeQueue,
                           vpiGenScopeArray, vpiGenScope};
  for (int type : kExcepted) {
    VpiObject obj;
    obj.type = type;
    obj.file = "ignored.sv";
    EXPECT_EQ(vpi_get_str(vpiFile, VpiHandleOf(&obj)), nullptr)
        << "object type " << type << " must not report a vpiFile";
    EXPECT_FALSE(VpiHasLocationProperties(type));
  }
}

int g_net_line = 0;
std::string g_net_file;
int g_var_line = 0;
int g_top_net_line = 0;
int g_port_line = 0;

PLI_INT32 ReadLocationsCalltf(PLI_BYTE8*) {
  vpiHandle net = vpi_handle_by_name(VpiText("m1.w"), nullptr);
  if (net != nullptr) {
    g_net_line = vpi_get(vpiLineNo, net);
    const char* file = vpi_get_str(vpiFile, net);
    if (file != nullptr) g_net_file = file;
  }
  vpiHandle var = vpi_handle_by_name(VpiText("m1.r"), nullptr);
  if (var != nullptr) g_var_line = vpi_get(vpiLineNo, var);
  vpiHandle top_net = vpi_handle_by_name(VpiText("top_sig"), nullptr);
  if (top_net != nullptr) g_top_net_line = vpi_get(vpiLineNo, top_net);

  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiPort, mod);
  if (itr == nullptr) return 0;
  vpiHandle port = vpi_scan(itr);
  if (port != nullptr) g_port_line = vpi_get(vpiLineNo, port);
  while (vpi_scan(itr) != nullptr) {
  }
  return 0;
}

void RegisterLocationProbe() {
  g_net_line = 0;
  g_net_file.clear();
  g_var_line = 0;
  g_top_net_line = 0;
  g_port_line = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadLocationsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunADesignOfLocatedDeclarations(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m(input a);\n"
      "  wire w;\n"
      "  reg r;\n"
      "endmodule\n"
      "module t;\n"
      "  wire top_sig;\n"
      "  m m1(top_sig);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

void RunAJoinedDesign(SimFixture& f) {
  const uint32_t kA = f.mgr.AddFile("a.sv", "");
  const uint32_t kB = f.mgr.AddFile("b.sv", "");
  const std::string kText =
      "module m(input a);\n"
      "  wire w;\n"
      "  reg r;\n"
      "endmodule\n"
      "module t;\n"
      "  wire top_sig;\n"
      "  m m1(top_sig);\n"
      "  initial $probe;\n"
      "endmodule\n";
  std::vector<OutputLineOrigin> origins = {{kB, 3}, {kB, 7}, {kB, 8},
                                           {kB, 9}, {kA, 1}, {kA, 2},
                                           {kA, 3}, {kA, 4}, {kA, 5}};
  const uint32_t kJoined =
      f.mgr.AddPreprocessedFile("<preprocessed>", kText, std::move(origins));
  Lexer lexer(f.mgr.FileContent(kJoined), kJoined, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  Elaborator elab(f.arena, f.diag, parser.Parse());
  RtlirDesign* design = elab.Elaborate("t");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class VpiLocationInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiLocationInARun, ADeclaredNetReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_net_line, 2);
}

TEST_F(VpiLocationInARun, ADeclaredNetReportsTheFileItWasDeclaredIn) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_net_file, "<test>");
}

TEST_F(VpiLocationInARun, ADeclaredVariableReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_var_line, 3);
}

TEST_F(VpiLocationInARun, ADeclaredPortReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_port_line, 1);
}

TEST_F(VpiLocationInARun, ANetOfTheTopModuleReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_top_net_line, 6);
}

TEST_F(VpiLocationInARun, ADeclarationReportsTheFileItWasWrittenIn) {
  RegisterLocationProbe();

  SimFixture f;
  RunAJoinedDesign(f);

  EXPECT_EQ(g_net_file, "b.sv");
}

TEST_F(VpiLocationInARun, ADeclarationReportsItsLineInItsOwnFile) {
  RegisterLocationProbe();

  SimFixture f;
  RunAJoinedDesign(f);

  EXPECT_EQ(g_net_line, 7);
}

TEST_F(VpiLocationInARun, ADeclarationOfTheOtherFileReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunAJoinedDesign(f);

  EXPECT_EQ(g_top_net_line, 2);
}

std::vector<std::pair<int, std::string>>& WhereCallLocations() {
  static std::vector<std::pair<int, std::string>> locations;
  return locations;
}

PLI_INT32 WhereCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  const char* file = vpi_get_str(vpiFile, call);
  WhereCallLocations().emplace_back(vpi_get(vpiLineNo, call),
                                    file == nullptr ? "" : file);
  return 0;
}

TEST_F(VpiLocationInARun, ASystemTaskCallReportsItsOwnLineAndFile) {
  WhereCallLocations().clear();
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$where");
  data.calltf = &WhereCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task tk; $where; endtask\n"
      "  initial begin\n"
      "    $where;\n"
      "    tk();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(WhereCallLocations(), (std::vector<std::pair<int, std::string>>{
                                      {4, "<test>"}, {2, "<test>"}}));
}

class WrittenLinesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module m(input a, input b, output o, output y);\n"
        "  wire p;\n"
        "  and g(o, a, b);\n"
        "  assign p = a;\n"
        "  task t; endtask\n"
        "  class C; endclass\n"
        "  initial begin end\n"
        "  specify\n"
        "    (a => y) = 1;\n"
        "    $setup(a, posedge b, 2);\n"
        "  endspecify\n"
        "endmodule\n"
        "module top; reg a, b; wire o, y; m m1(a, b, o, y); endmodule\n");
  }

  static int LineOfFirst(int type) {
    vpiHandle it = vpi_iterate(type, By("top.m1"));
    vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it);
    return obj == nullptr ? -1 : vpi_get(vpiLineNo, obj);
  }
};

TEST_F(WrittenLinesOfARun, APrimitiveReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiPrimitive), 3);
}

TEST_F(WrittenLinesOfARun, AContinuousAssignmentReportsItsLine) {
  EXPECT_EQ(LineOfFirst(vpiContAssign), 4);
}

TEST_F(WrittenLinesOfARun, ATaskReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiTask), 5);
}

TEST_F(WrittenLinesOfARun, AClassDefnReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiClassDefn), 6);
}

TEST_F(WrittenLinesOfARun, AProcessReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiProcess), 7);
}

TEST_F(WrittenLinesOfARun, AModulePathReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiModPath), 9);
}

TEST_F(WrittenLinesOfARun, ATimingCheckReportsTheLineItWasWrittenOn) {
  EXPECT_EQ(LineOfFirst(vpiTchk), 10);
}

class ParameterLinesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("package pk;\n"
        "  parameter int Q = 4;\n"
        "  parameter type R = byte;\n"
        "endpackage\n"
        "module top #(\n"
        "  parameter int W = 1,\n"
        "  parameter type TP = int\n"
        ");\n"
        "  parameter int P = 3;\n"
        "  parameter type T = logic;\n"
        "endmodule\n");
  }

  static int LineOf(int type, const char* scope, std::string_view name) {
    vpiHandle obj = Named(type, By(scope), name);
    return obj == nullptr ? -1 : vpi_get(vpiLineNo, obj);
  }
};

TEST_F(ParameterLinesOfARun, AValueParameterOfTheBodyReportsItsLine) {
  EXPECT_EQ(LineOf(vpiParameter, "top", "P"), 9);
}

TEST_F(ParameterLinesOfARun, ATypeParameterOfTheBodyReportsItsLine) {
  EXPECT_EQ(LineOf(vpiTypeParameter, "top", "T"), 10);
}

TEST_F(ParameterLinesOfARun, AValueParameterPortReportsItsLine) {
  EXPECT_EQ(LineOf(vpiParameter, "top", "W"), 6);
}

TEST_F(ParameterLinesOfARun, ATypeParameterPortReportsItsLine) {
  EXPECT_EQ(LineOf(vpiTypeParameter, "top", "TP"), 7);
}

TEST_F(ParameterLinesOfARun, AValueParameterOfAPackageReportsItsLine) {
  EXPECT_EQ(LineOf(vpiParameter, "pk", "Q"), 2);
}

TEST_F(ParameterLinesOfARun, ATypeParameterOfAPackageReportsItsLine) {
  EXPECT_EQ(LineOf(vpiTypeParameter, "pk", "R"), 3);
}

TEST_F(ParameterLinesOfARun, AParameterReportsTheFileItWasWrittenIn) {
  vpiHandle param = Named(vpiParameter, By("top"), "P");
  ASSERT_NE(param, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFile, param), "<test>");
}

}  // namespace
}  // namespace delta
