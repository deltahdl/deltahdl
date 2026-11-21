#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TimingCheck : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(TimingCheck, RefAndDataTermsAreReached) {
  VpiObject ref_term;
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;
  data_term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  tchk.tchk_data_term = &data_term;

  VpiHandle reached_ref =
      VpiObjectOf(vpi_handle(vpiTchkRefTerm, VpiHandleOf(&tchk)));
  VpiHandle reached_data =
      VpiObjectOf(vpi_handle(vpiTchkDataTerm, VpiHandleOf(&tchk)));
  EXPECT_EQ(reached_ref, &ref_term);
  EXPECT_EQ(reached_data, &data_term);

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_ref)), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_data)), vpiTchkTerm);
}

TEST_F(TimingCheck, DataTermIsNullWhenCheckHasNoDataEvent) {
  VpiObject ref_term;
  ref_term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTchkRefTerm, VpiHandleOf(&tchk))),
            &ref_term);
  EXPECT_EQ(vpi_handle(vpiTchkDataTerm, VpiHandleOf(&tchk)), nullptr);
}

TEST_F(TimingCheck, TermRelationsApplyOnlyToTimingChecks) {
  VpiObject stray_term;
  stray_term.type = vpiTchkTerm;

  VpiObject not_a_tchk;
  not_a_tchk.type = vpiModule;
  not_a_tchk.children = {&stray_term};

  EXPECT_EQ(vpi_handle(vpiTchkRefTerm, VpiHandleOf(&not_a_tchk)), nullptr);
  EXPECT_EQ(vpi_handle(vpiTchkDataTerm, VpiHandleOf(&not_a_tchk)), nullptr);
}

TEST_F(TimingCheck, ExprIterationReturnsTheArgumentsInOrder) {
  VpiObject ref_term;
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;
  data_term.type = vpiTchkTerm;
  VpiObject limit;
  limit.type = vpiOperation;
  VpiObject notifier;
  notifier.type = vpiReg;
  VpiObject stray;
  stray.type = vpiConstant;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  tchk.tchk_data_term = &data_term;
  tchk.children = {&ref_term, &data_term, &stray};
  tchk.tchk_arguments = {&data_term, &ref_term, &limit, &notifier};

  vpiHandle it = vpi_iterate(vpiExpr, VpiHandleOf(&tchk));
  ASSERT_NE(it, nullptr);
  std::vector<VpiObject*> reached;
  while (vpiHandle h = vpi_scan(it)) reached.push_back(VpiObjectOf(h));
  EXPECT_EQ(reached, (std::vector<VpiObject*>{&data_term, &ref_term, &limit,
                                              &notifier}));
}

TEST_F(TimingCheck, ExprIterationIsNullWhenNoArguments) {
  VpiObject term;
  term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.children = {&term};

  EXPECT_EQ(vpi_iterate(vpiExpr, VpiHandleOf(&tchk)), nullptr);
}

int g_tchks_seen = 0;
int g_tchk_type = 0;
std::string g_ref_term_name;
std::string g_data_term_name;
int g_ref_term_edge = -1;
std::string g_notifier_name;
int g_limit = -1;

std::string NameOf(vpiHandle obj) {
  if (obj == nullptr) return std::string();
  const char* name = vpi_get_str(vpiName, obj);
  return name == nullptr ? std::string() : std::string(name);
}

int LimitOf(vpiHandle tchk) {
  s_vpi_delay delays = {};
  s_vpi_time times[1] = {};
  delays.da = times;
  delays.no_of_delays = 1;
  delays.time_type = vpiSimTime;
  vpi_get_delays(tchk, &delays);
  return static_cast<int>(times[0].low);
}

void ReadOneTimingCheck(vpiHandle tchk) {
  ++g_tchks_seen;
  g_tchk_type = vpi_get(vpiTchkType, tchk);

  vpiHandle ref = vpi_handle(vpiTchkRefTerm, tchk);
  g_ref_term_name = NameOf(ref);
  g_ref_term_edge = ref == nullptr ? -1 : vpi_get(vpiEdge, ref);
  g_data_term_name = NameOf(vpi_handle(vpiTchkDataTerm, tchk));
  g_notifier_name = NameOf(vpi_handle(vpiTchkNotifier, tchk));
  g_limit = LimitOf(tchk);
}

PLI_INT32 ProbeTimingChecksCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiTchk, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle tchk = vpi_scan(itr)) ReadOneTimingCheck(tchk);
  return 0;
}

TEST(TimingCheckDesign, ADeclaredTimingCheckIsATchkObject) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_tchks_seen = 0;
  g_tchk_type = 0;
  g_ref_term_name.clear();
  g_data_term_name.clear();
  g_ref_term_edge = -1;
  g_notifier_name.clear();
  g_limit = -1;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeTimingChecksCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input d);\n"
      "  reg notifier;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, notifier);\n"
      "  endspecify\n"
      "endmodule\n"
      "module t;\n"
      "  reg clk, d;\n"
      "  m m1(clk, d);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_tchks_seen, 1);
  EXPECT_EQ(g_tchk_type, vpiSetup);
  EXPECT_EQ(g_ref_term_name, "clk");
  EXPECT_EQ(g_data_term_name, "d");
  EXPECT_EQ(g_ref_term_edge, vpiPosedge);
  EXPECT_EQ(g_notifier_name, "notifier");
  EXPECT_EQ(g_limit, 5);
}

class TimingChecksOfARun : public VpiDesignRun {};

TEST_F(TimingChecksOfARun, EveryCheckKindReportsItsTchkType) {
  Run("module m(input clk, input d);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 1);\n"
      "    $hold(posedge clk, d, 1);\n"
      "    $setuphold(posedge clk, d, 1, 1);\n"
      "    $recovery(posedge clk, d, 1);\n"
      "    $removal(posedge clk, d, 1);\n"
      "    $recrem(posedge clk, d, 1, 1);\n"
      "    $width(negedge clk, 2);\n"
      "    $period(posedge clk, 4);\n"
      "    $skew(posedge clk, d, 1);\n"
      "    $nochange(posedge clk, d, 0, 0);\n"
      "    $timeskew(posedge clk, d, 1);\n"
      "    $fullskew(posedge clk, d, 1, 1);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d; m m1(clk, d); endmodule\n");
  std::vector<int> types;
  vpiHandle width = nullptr;
  vpiHandle it = vpi_iterate(vpiTchk, By("top.m1"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle tchk = vpi_scan(it)) {
    types.push_back(vpi_get(vpiTchkType, tchk));
    if (types.back() == vpiWidth) width = tchk;
    EXPECT_EQ(vpi_handle(vpiTchkNotifier, tchk), nullptr);
  }
  std::sort(types.begin(), types.end());
  std::vector<int> expected = {
      vpiSetup, vpiHold,   vpiSetupHold, vpiRecovery, vpiRemoval,  vpiRecrem,
      vpiWidth, vpiPeriod, vpiSkew,      vpiNoChange, vpiTimeskew, vpiFullskew};
  std::sort(expected.begin(), expected.end());
  EXPECT_EQ(types, expected);
  ASSERT_NE(width, nullptr);
  EXPECT_EQ(vpi_handle(vpiTchkDataTerm, width), nullptr);
  vpiHandle ref = vpi_handle(vpiTchkRefTerm, width);
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(vpi_get(vpiEdge, ref), vpiNegedge);
}

int CountOf(int type, vpiHandle ref) {
  int count = 0;
  vpiHandle it = vpi_iterate(type, ref);
  if (it == nullptr) return 0;
  while (vpi_scan(it) != nullptr) ++count;
  return count;
}

TEST_F(TimingChecksOfARun, ATopModulesSpecifyBlockHangsFromTheTop) {
  Run("module leaf(input c, output e);\n"
      "  assign e = c;\n"
      "  specify (c => e) = 1; $width(posedge c, 1); endspecify\n"
      "endmodule\n"
      "module top(input a, output b);\n"
      "  assign b = a;\n"
      "  leaf u(.c(a), .e());\n"
      "  specify (a => b) = 2; $width(negedge a, 2); endspecify\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiModPath, By("top")), 1);
  EXPECT_EQ(CountOf(vpiTchk, By("top")), 1);
  EXPECT_EQ(CountOf(vpiModPath, By("top.u")), 1);
  EXPECT_EQ(CountOf(vpiTchk, By("top.u")), 1);
}

vpiHandle CheckOfType(int type, vpiHandle inst) {
  vpiHandle it = vpi_iterate(vpiTchk, inst);
  if (it == nullptr) return nullptr;
  while (vpiHandle tchk = vpi_scan(it)) {
    if (vpi_get(vpiTchkType, tchk) == type) return tchk;
  }
  return nullptr;
}

TEST_F(TimingChecksOfARun, ATchkTermReachesItsExpressionAndCondition) {
  Run("module m(input clk, input en, input [3:0] bus);\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, bus[2:1], 1);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, en; reg [3:0] bus; m m1(clk, en, bus); "
      "endmodule\n");
  vpiHandle hold = CheckOfType(vpiHold, By("top.m1"));
  ASSERT_NE(hold, nullptr);
  vpiHandle ref = vpi_handle(vpiTchkRefTerm, hold);
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(NameOf(vpi_handle(vpiExpr, ref)), "clk");
  EXPECT_EQ(NameOf(vpi_handle(vpiCondition, ref)), "en");

  vpiHandle data = vpi_handle(vpiTchkDataTerm, hold);
  ASSERT_NE(data, nullptr);
  vpiHandle selected = vpi_handle(vpiExpr, data);
  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(vpi_get(vpiType, selected), vpiPartSelect);
  EXPECT_EQ(NameOf(vpi_handle(vpiParent, selected)), "bus");
  EXPECT_EQ(vpi_handle(vpiCondition, data), nullptr);
  EXPECT_EQ(vpi_handle(vpiCondition, hold), nullptr);
  EXPECT_EQ(vpi_handle(vpiTchkNotifier, ref), nullptr);
}

std::vector<int> DelaysOf(vpiHandle tchk, int count) {
  s_vpi_time times[2] = {};
  s_vpi_delay delays = {};
  delays.da = times;
  delays.no_of_delays = count;
  delays.time_type = vpiSimTime;
  times[0].low = 99;
  vpi_get_delays(tchk, &delays);
  std::vector<int> read;
  if (times[0].low == 99) return read;
  for (int i = 0; i < count; ++i)
    read.push_back(static_cast<int>(times[i].low));
  return read;
}

TEST_F(TimingChecksOfARun, EveryLimitOfACheckIsADelay) {
  Run("module m(input clk, input d);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, 3, 7);\n"
      "    $width(posedge clk, 6, 2);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d; m m1(clk, d); endmodule\n");
  vpiHandle setuphold = CheckOfType(vpiSetupHold, By("top.m1"));
  ASSERT_NE(setuphold, nullptr);
  EXPECT_EQ(DelaysOf(setuphold, 2), (std::vector<int>{3, 7}));
  EXPECT_TRUE(DelaysOf(setuphold, 1).empty());
  vpiHandle width = CheckOfType(vpiWidth, By("top.m1"));
  ASSERT_NE(width, nullptr);
  EXPECT_EQ(DelaysOf(width, 1), (std::vector<int>{6}));
  EXPECT_TRUE(DelaysOf(width, 2).empty());
}

bool RefusesDelays(vpiHandle tchk, int count) {
  s_vpi_time times[2] = {};
  s_vpi_delay delays = {};
  delays.da = times;
  delays.no_of_delays = count;
  delays.time_type = vpiSimTime;
  vpi_get_delays(tchk, &delays);
  s_vpi_error_info info = {};
  return vpi_chk_error(&info) != 0;
}

TEST_F(TimingChecksOfARun, ANochangeHasNoDelaysToRead) {
  Run("module m(input clk, input d);\n"
      "  specify\n"
      "    $nochange(posedge clk, d, 2, 3);\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d; m m1(clk, d); endmodule\n");
  vpiHandle nochange = CheckOfType(vpiNoChange, By("top.m1"));
  ASSERT_NE(nochange, nullptr);
  EXPECT_TRUE(RefusesDelays(nochange, 0));
  EXPECT_TRUE(RefusesDelays(nochange, 1));
  EXPECT_TRUE(RefusesDelays(nochange, 2));
  vpiHandle hold = CheckOfType(vpiHold, By("top.m1"));
  ASSERT_NE(hold, nullptr);
  EXPECT_TRUE(RefusesDelays(hold, 0));
  EXPECT_FALSE(RefusesDelays(hold, 1));
}

int EdgeOf(int relation, vpiHandle tchk) {
  vpiHandle term = vpi_handle(relation, tchk);
  return term == nullptr ? -1 : vpi_get(vpiEdge, term);
}

TEST_F(TimingChecksOfARun, ATchkTermReportsTheTransitionsItsEventLists) {
  Run("module m(input clk, input d);\n"
      "  specify\n"
      "    $setup(d, edge [01, 0x] clk, 1);\n"
      "    $hold(edge [10, z0] clk, edge d, 1);\n"
      "    $width(edge [x1, 1x] clk, 2);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d; m m1(clk, d); endmodule\n");
  vpiHandle setup = CheckOfType(vpiSetup, By("top.m1"));
  ASSERT_NE(setup, nullptr);
  EXPECT_EQ(EdgeOf(vpiTchkRefTerm, setup), vpiEdge01 | vpiEdge0x);
  EXPECT_EQ(EdgeOf(vpiTchkDataTerm, setup), vpiNoEdge);
  vpiHandle hold = CheckOfType(vpiHold, By("top.m1"));
  ASSERT_NE(hold, nullptr);
  EXPECT_EQ(EdgeOf(vpiTchkRefTerm, hold), vpiEdge10 | vpiEdgex0);
  EXPECT_EQ(EdgeOf(vpiTchkDataTerm, hold), vpiAnyEdge);
  vpiHandle width = CheckOfType(vpiWidth, By("top.m1"));
  ASSERT_NE(width, nullptr);
  EXPECT_EQ(EdgeOf(vpiTchkRefTerm, width), vpiEdgex1 | vpiEdge1x);
}

std::vector<std::pair<int, std::string>> ArgumentsOf(vpiHandle tchk) {
  std::vector<std::pair<int, std::string>> found;
  vpiHandle it = vpi_iterate(vpiExpr, tchk);
  if (it == nullptr) return found;
  while (vpiHandle arg = vpi_scan(it)) {
    const int kType = vpi_get(vpiType, arg);
    if (kType != vpiConstant) {
      found.emplace_back(kType, NameOf(arg));
      continue;
    }
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(arg, &value);
    found.emplace_back(kType, std::to_string(value.value.integer));
  }
  return found;
}

TEST_F(TimingChecksOfARun, ACheckIteratesEveryArgumentAsWritten) {
  Run("module m(input clk, input d, input en);\n"
      "  reg ntfr, dclk, dd;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 3);\n"
      "    $setuphold(posedge clk, d, 1, 2, ntfr, en, , dclk, dd);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d, en; m m1(clk, d, en); endmodule\n");
  using Arg = std::pair<int, std::string>;
  EXPECT_EQ(ArgumentsOf(CheckOfType(vpiSetup, By("top.m1"))),
            (std::vector<Arg>{
                {vpiTchkTerm, "d"}, {vpiTchkTerm, "clk"}, {vpiConstant, "3"}}));
  vpiHandle setuphold = CheckOfType(vpiSetupHold, By("top.m1"));
  vpiHandle notifier = vpi_handle(vpiTchkNotifier, setuphold);
  ASSERT_NE(notifier, nullptr);
  const int kReg = vpi_get(vpiType, notifier);
  EXPECT_EQ(ArgumentsOf(setuphold),
            (std::vector<Arg>{{vpiTchkTerm, "clk"},
                              {vpiTchkTerm, "d"},
                              {vpiConstant, "1"},
                              {vpiConstant, "2"},
                              {kReg, "ntfr"},
                              {vpi_get(vpiType, By("top.m1.en")), "en"},
                              {kReg, "dclk"},
                              {kReg, "dd"}}));
}

TEST_F(TimingChecksOfARun, ABitOfAVectorIsATermsAndADelayedSignalsExpression) {
  Run("module m(input clk, input [1:0] d);\n"
      "  reg ntfr, dclk; reg [1:0] dd;\n"
      "  specify\n"
      "    $setuphold(posedge clk, d[1], 1, 2, ntfr, , , dclk, dd[1]);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk; reg [1:0] d; m m1(clk, d); endmodule\n");
  vpiHandle setuphold = CheckOfType(vpiSetupHold, By("top.m1"));
  ASSERT_NE(setuphold, nullptr);
  vpiHandle data = vpi_handle(vpiExpr, vpi_handle(vpiTchkDataTerm, setuphold));
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(NameOf(data), "d[1]");
  EXPECT_EQ(NameOf(vpi_handle(vpiParent, data)), "d");
  const std::vector<std::pair<int, std::string>> kArgs = ArgumentsOf(setuphold);
  ASSERT_FALSE(kArgs.empty());
  EXPECT_EQ(kArgs.back().second, "dd[1]");
}

TEST_F(TimingChecksOfARun, AnInterfacePortMemberIsATermsExpression) {
  Run("interface bus;\n"
      "  logic clk, d;\n"
      "endinterface\n"
      "module dut(bus b);\n"
      "  specify\n"
      "    $hold(posedge b.clk, b.d, 1);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; bus b(); dut u(b); endmodule\n");
  vpiHandle hold = CheckOfType(vpiHold, By("top.u"));
  ASSERT_NE(hold, nullptr);
  EXPECT_EQ(NameOf(vpi_handle(vpiExpr, vpi_handle(vpiTchkRefTerm, hold))),
            "clk");
  EXPECT_EQ(NameOf(vpi_handle(vpiExpr, vpi_handle(vpiTchkDataTerm, hold))),
            "d");
}

TEST(TimingCheckDesign, AnEntryOfNoLoweredTopHangsFromNothing) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  SimFixture f;
  SpecifyManager specify;
  specify.AddPathDelay(PathDelay{});
  specify.AddTimingCheck(TimingCheckEntry{});
  f.ctx.SetSpecifyManager(&specify);
  vpi_ctx.Attach(f.ctx);
  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
