#include <gtest/gtest.h>

#include <algorithm>
#include <string>
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

// §37.40 Timing check: the object model diagram for a timing check (the "tchk"
// node) and its event terms (the "tchk term" node). The subclause carries two
// numbered Details. Detail 1 fixes what the vpiTchkRefTerm and vpiTchkDataTerm
// relations denote - the reference (or controlled-reference) event and the data
// event, the latter only when the check has one. Detail 2 fixes the types the
// vpiExpr iteration over a tchk returns - vpiTchkTerm for the event arguments
// and the natural expression type for every other argument. These tests observe
// the production code that applies those two rules through the public
// vpi_handle and vpi_iterate dispatch.

// The fixture installs a context so the public vpi_handle/vpi_iterate entry
// points run their real dispatch over the test objects.
class TimingCheck : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: vpiTchkRefTerm reaches the timing check's reference (or
// controlled-reference) event term and vpiTchkDataTerm reaches its data event
// term. Both terms are tchk term objects, whose own type differs from the
// relation enum, so the relations resolve to the check's designated terms.
TEST_F(TimingCheck, RefAndDataTermsAreReached) {
  VpiObject ref_term;  // the reference / controlled-reference event
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;  // the data event
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

  // The handles returned for the events have the tchk term type.
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_ref)), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_data)), vpiTchkTerm);
}

// Detail 1 (the data event being optional): a timing check that has no data
// event reports NULL for vpiTchkDataTerm, while its reference term is still
// reached.
TEST_F(TimingCheck, DataTermIsNullWhenCheckHasNoDataEvent) {
  VpiObject ref_term;
  ref_term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  // tchk_data_term left null: this check has no data event.

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTchkRefTerm, VpiHandleOf(&tchk))),
            &ref_term);
  EXPECT_EQ(vpi_handle(vpiTchkDataTerm, VpiHandleOf(&tchk)), nullptr);
}

// Detail 1 (scope): the vpiTchkRefTerm/vpiTchkDataTerm relations are specific
// to a timing check. On an object that is not a tchk, asking for them does not
// reach a stray tchk term, so the relations report NULL even when the object
// carries a tchk term child.
TEST_F(TimingCheck, TermRelationsApplyOnlyToTimingChecks) {
  VpiObject stray_term;
  stray_term.type = vpiTchkTerm;

  VpiObject not_a_tchk;
  not_a_tchk.type = vpiModule;
  not_a_tchk.children = {&stray_term};

  EXPECT_EQ(vpi_handle(vpiTchkRefTerm, VpiHandleOf(&not_a_tchk)), nullptr);
  EXPECT_EQ(vpi_handle(vpiTchkDataTerm, VpiHandleOf(&not_a_tchk)), nullptr);
}

// Detail 2: iterating vpiExpr over a timing check returns its arguments - the
// reference, controlled-reference, and data events as tchk term handles, and
// every other argument with the type of its expression. A non-argument child
// (the notifier register) is not reached by this relation.
TEST_F(TimingCheck, ExprIterationReturnsTermsAndExpressions) {
  VpiObject ref_term;  // a reference event -> vpiTchkTerm
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;  // a data event -> vpiTchkTerm
  data_term.type = vpiTchkTerm;
  VpiObject limit;  // a limit argument expression -> its own expr type
  limit.type = vpiOperation;
  VpiObject notifier;  // the notifier register: not an expr argument
  notifier.type = vpiReg;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  tchk.tchk_data_term = &data_term;
  tchk.children = {&ref_term, &notifier, &data_term, &limit};

  vpiHandle it = vpi_iterate(vpiExpr, VpiHandleOf(&tchk));
  ASSERT_NE(it, nullptr);

  int count = 0;
  bool saw_ref = false;
  bool saw_data = false;
  bool saw_limit = false;
  bool saw_notifier = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (VpiObjectOf(h) == &ref_term) saw_ref = true;
    if (VpiObjectOf(h) == &data_term) saw_data = true;
    if (VpiObjectOf(h) == &limit) saw_limit = true;
    if (VpiObjectOf(h) == &notifier) saw_notifier = true;
  }

  EXPECT_EQ(count, 3);
  EXPECT_TRUE(saw_ref);
  EXPECT_TRUE(saw_data);
  EXPECT_TRUE(saw_limit);
  EXPECT_FALSE(saw_notifier);  // the notifier reg is not an expr argument

  // The event arguments are returned with the tchk term type; the other
  // argument keeps the type of its expression.
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&ref_term)), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&data_term)), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&limit)), vpiOperation);
}

// Detail 2 (edge): a timing check whose only children are non-argument objects
// has nothing for the vpiExpr iteration to walk, so vpi_iterate reports a null
// handle rather than an iterator that scans to nothing.
TEST_F(TimingCheck, ExprIterationIsNullWhenNoArguments) {
  VpiObject notifier;
  notifier.type = vpiReg;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.children = {&notifier};

  EXPECT_EQ(vpi_iterate(vpiExpr, VpiHandleOf(&tchk)), nullptr);
}

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
int g_tchks_seen = 0;
int g_tchk_type = 0;
std::string g_ref_term_name;
std::string g_data_term_name;
int g_ref_term_edge = -1;
std::string g_notifier_name;
int g_limit = -1;

// The name an object reports, or the empty string where it reports none.
std::string NameOf(vpiHandle obj) {
  if (obj == nullptr) return std::string();
  const char* name = vpi_get_str(vpiName, obj);
  return name == nullptr ? std::string() : std::string(name);
}

// The figure's "-> limit", retrieved the way the diagram says it is.
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

// §37.40 against a design. Every property and relation the figure draws is
// drawn on a tchk, and no pass built one, so a module's vpiTchk iteration
// reached none of the checks its specify block declared and the whole of the
// subclause answered for objects a test had made.
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
  // The figure's "-> tchk type" property, which is §31.2's $setup.
  EXPECT_EQ(g_tchk_type, vpiSetup);
  // Detail 1: the reference event of $setup is its second argument and the data
  // event its first.
  EXPECT_EQ(g_ref_term_name, "clk");
  EXPECT_EQ(g_data_term_name, "d");
  // The tchk term's "-> edge" property: the reference event was written
  // posedge.
  EXPECT_EQ(g_ref_term_edge, vpiPosedge);
  // The figure's vpiTchkNotifier relation.
  EXPECT_EQ(g_notifier_name, "notifier");
  // The figure's "-> limit", retrieved with vpi_get_delays().
  EXPECT_EQ(g_limit, 5);
}

class TimingChecksOfARun : public VpiDesignRun {};

// §37.40 (figure): a tchk reports which of §31.2's checks it is through
// vpiTchkType, one constant per check. Detail 1: a check with no data event,
// as $width has, reaches no data term, and its reference term carries the edge
// it was written with. A check written without a notifier reaches none.
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

// The objects of `type` `ref` reaches, counted.
int CountOf(int type, vpiHandle ref) {
  int count = 0;
  vpiHandle it = vpi_iterate(type, ref);
  if (it == nullptr) return 0;
  while (vpi_scan(it) != nullptr) ++count;
  return count;
}

// §37.39 and §37.40 with §30.3 and §31.1: a specify block belongs to the module
// declaring it, a top module among them, so the top reaches its own path and
// check while the instance it holds reaches the instance's.
TEST_F(TimingChecksOfARun, ATopModulesSpecifyBlockHangsFromTheTop) {
  Run("module cell(input c, output e);\n"
      "  assign e = c;\n"
      "  specify (c => e) = 1; $width(posedge c, 1); endspecify\n"
      "endmodule\n"
      "module top(input a, output b);\n"
      "  assign b = a;\n"
      "  cell u(.c(a), .e());\n"
      "  specify (a => b) = 2; $width(negedge a, 2); endspecify\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiModPath, By("top")), 1);
  EXPECT_EQ(CountOf(vpiTchk, By("top")), 1);
  EXPECT_EQ(CountOf(vpiModPath, By("top.u")), 1);
  EXPECT_EQ(CountOf(vpiTchk, By("top.u")), 1);
}

// A path or check filed under the empty prefix belongs to the first top the
// run lowered; with no top lowered there is no module for it to hang from.
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
