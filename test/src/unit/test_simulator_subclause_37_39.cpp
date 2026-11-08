#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "parser/ast_specify.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ModulePathModel : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle MakeObject(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("mp", "mp");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

TEST_F(ModulePathModel, ModuleReachedFromPathInModule) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  VpiHandle path = MakeObject(vpiModPath);
  path->parent = mod;
  mod->children.push_back(path);

  VpiHandle reached = VpiObjectOf(vpi_handle(kVpiModule, VpiHandleOf(path)));
  EXPECT_EQ(reached, mod);
}

TEST_F(ModulePathModel, ModuleIsNullForInterfaceNestedInModule) {
  auto* outer = vpi_ctx_.CreateModule("wrap", "wrap");
  VpiHandle iface = MakeObject(vpiInterface);
  iface->parent = outer;
  outer->children.push_back(iface);

  VpiHandle path = MakeObject(vpiModPath);
  path->parent = iface;
  iface->children.push_back(path);

  EXPECT_EQ(vpi_handle(kVpiModule, VpiHandleOf(path)), nullptr);
}

TEST_F(ModulePathModel, CarveOutAppliesOnlyToModPath) {
  auto* mod = vpi_ctx_.CreateModule("host", "host");
  VpiHandle other = MakeObject(vpiNet);
  other->parent = mod;
  mod->children.push_back(other);

  EXPECT_EQ(VpiObjectOf(vpi_handle(kVpiModule, VpiHandleOf(other))), mod);
}

TEST_F(ModulePathModel, ModuleIsNullWhenNoInstanceEncloses) {
  VpiHandle scope = MakeObject(vpiNamedBegin);
  VpiHandle path = MakeObject(vpiModPath);
  path->parent = scope;
  scope->children.push_back(path);

  EXPECT_EQ(vpi_handle(kVpiModule, VpiHandleOf(path)), nullptr);
}

TEST_F(ModulePathModel, AModulePathReportsItsOwnProperties) {
  VpiObject path;
  path.type = vpiModPath;
  path.path_type = vpiPathParallel;
  path.polarity = vpiPositive;
  path.data_polarity = vpiNegative;
  path.mod_path_has_if_none = true;

  EXPECT_EQ(vpi_get(vpiPathType, VpiHandleOf(&path)), vpiPathParallel);
  EXPECT_EQ(vpi_get(vpiPolarity, VpiHandleOf(&path)), vpiPositive);
  EXPECT_EQ(vpi_get(vpiDataPolarity, VpiHandleOf(&path)), vpiNegative);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, VpiHandleOf(&path)), 1);

  VpiObject full;
  full.type = vpiModPath;
  full.path_type = vpiPathFull;
  EXPECT_EQ(vpi_get(vpiPathType, VpiHandleOf(&full)), vpiPathFull);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, VpiHandleOf(&full)), 0);
}

TEST_F(ModulePathModel, APathTermReportsItsEdgeAndDirection) {
  VpiObject term;
  term.type = vpiPathTerm;
  term.direction = kVpiInput;
  term.edge = vpiEdge01;

  EXPECT_EQ(vpi_get(vpiEdge, VpiHandleOf(&term)), vpiEdge01);
  EXPECT_EQ(vpi_get(kVpiDirection, VpiHandleOf(&term)), kVpiInput);
}

TEST_F(ModulePathModel, TheThreeTermRelationsReachTheirOwnTerms) {
  VpiObject in_term;
  in_term.type = vpiPathTerm;
  in_term.direction = kVpiInput;
  VpiObject data_term;
  data_term.type = vpiPathTerm;
  data_term.direction = kVpiInput;
  data_term.data_path_term = true;
  VpiObject out_term;
  out_term.type = vpiPathTerm;
  out_term.direction = kVpiOutput;
  VpiObject not_a_term;
  not_a_term.type = vpiConstant;

  VpiObject path;
  path.type = vpiModPath;
  path.children = {&in_term, &data_term, &out_term, &not_a_term};

  vpiHandle ins = vpi_iterate(vpiModPathIn, VpiHandleOf(&path));
  ASSERT_NE(ins, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(ins)), &in_term);
  EXPECT_EQ(vpi_scan(ins), nullptr);

  vpiHandle datas = vpi_iterate(vpiModDataPathIn, VpiHandleOf(&path));
  ASSERT_NE(datas, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(datas)), &data_term);
  EXPECT_EQ(vpi_scan(datas), nullptr);

  vpiHandle outs = vpi_iterate(vpiModPathOut, VpiHandleOf(&path));
  ASSERT_NE(outs, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(outs)), &out_term);
  EXPECT_EQ(vpi_scan(outs), nullptr);
}

TEST_F(ModulePathModel, ARelationWithNoTermOfItsRoleReachesNone) {
  VpiObject out_term;
  out_term.type = vpiPathTerm;
  out_term.direction = kVpiOutput;

  VpiObject path;
  path.type = vpiModPath;
  path.children = {&out_term};

  EXPECT_EQ(vpi_iterate(vpiModPathIn, VpiHandleOf(&path)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiModDataPathIn, VpiHandleOf(&path)), nullptr);
  EXPECT_NE(vpi_iterate(vpiModPathOut, VpiHandleOf(&path)), nullptr);
}

class ModulePathsOfARun : public VpiDesignRun {};

std::string NameOf(vpiHandle obj) {
  if (obj == nullptr) return std::string();
  const char* name = vpi_get_str(vpiName, obj);
  return name == nullptr ? std::string() : std::string(name);
}

std::vector<std::pair<std::string, int>> TermsOf(int relation, vpiHandle path) {
  std::vector<std::pair<std::string, int>> terms;
  vpiHandle it = vpi_iterate(relation, path);
  if (it == nullptr) return terms;
  while (vpiHandle term = vpi_scan(it)) {
    const bool kOwn = vpi_compare_objects(vpi_handle(vpiModPath, term), path);
    terms.emplace_back(kOwn ? NameOf(vpi_handle(vpiExpr, term)) : "",
                       vpi_get(vpiEdge, term));
  }
  return terms;
}

using Term = std::pair<std::string, int>;

TEST_F(ModulePathsOfARun, APathsTermsAreWhatItWasWrittenWith) {
  Run("module m(input clk, input d, input a, input b, output q, "
      "output y);\n"
      "  specify\n"
      "    (posedge clk => (q +: d)) = 2;\n"
      "    (a, b *> y) = 1;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d, a, b; wire q, y; m m1(clk, d, a, b, q, y); "
      "endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top.m1"));
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[0]),
            (std::vector<Term>{{"clk", vpiPosedge}}));
  EXPECT_EQ(TermsOf(vpiModPathOut, kPaths[0]),
            (std::vector<Term>{{"q", vpiNoEdge}}));
  EXPECT_EQ(TermsOf(vpiModDataPathIn, kPaths[0]),
            (std::vector<Term>{{"d", vpiNoEdge}}));

  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[1]),
            (std::vector<Term>{{"a", vpiNoEdge}}));
  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[2]),
            (std::vector<Term>{{"b", vpiNoEdge}}));
  for (vpiHandle full : {kPaths[1], kPaths[2]}) {
    EXPECT_EQ(TermsOf(vpiModPathOut, full),
              (std::vector<Term>{{"y", vpiNoEdge}}));
    EXPECT_TRUE(TermsOf(vpiModDataPathIn, full).empty());
  }
}

TEST_F(ModulePathsOfARun, APathTermReportsItsDirection) {
  Run("module m(input clk, input d, output q);\n"
      "  specify\n"
      "    (negedge clk => (q -: d)) = 2;\n"
      "    (edge clk => (q : d)) = 3;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d; wire q; m m1(clk, d, q); endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top.m1"));
  ASSERT_EQ(kPaths.size(), 2u);
  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[0]),
            (std::vector<Term>{{"clk", vpiNegedge}}));
  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[1]),
            (std::vector<Term>{{"clk", vpiAnyEdge}}));
  for (const int kRelation : {vpiModPathIn, vpiModDataPathIn}) {
    const std::vector<vpiHandle> kTerms = ObjectsOf(kRelation, kPaths[0]);
    ASSERT_EQ(kTerms.size(), 1u);
    EXPECT_EQ(vpi_get(kVpiDirection, kTerms[0]), kVpiInput);
  }
  const std::vector<vpiHandle> kOut = ObjectsOf(vpiModPathOut, kPaths[0]);
  ASSERT_EQ(kOut.size(), 1u);
  EXPECT_EQ(vpi_get(kVpiDirection, kOut[0]), kVpiOutput);
}

TEST_F(ModulePathsOfARun, AStateDependentPathReachesItsCondition) {
  Run("module m(input s, input a, output y, output z);\n"
      "  specify\n"
      "    if (s) (a => y) = 1;\n"
      "    ifnone (a => y) = 2;\n"
      "    (a => z) = 3;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg s, a; wire y, z; m m1(s, a, y, z); endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top.m1"));
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(NameOf(vpi_handle(vpiCondition, kPaths[0])), "s");
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, kPaths[0]), 0);
  EXPECT_EQ(vpi_handle(vpiCondition, kPaths[1]), nullptr);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, kPaths[1]), 1);
  EXPECT_EQ(vpi_handle(vpiCondition, kPaths[2]), nullptr);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, kPaths[2]), 0);
}

TEST_F(ModulePathsOfARun, ABitOfAVectorIsATermsAndAConditionsExpression) {
  Run("module m(input [1:0] s, input [1:0] a, output [1:0] b);\n"
      "  specify\n"
      "    if (s[1]) (a[0] => b[1]) = 1;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg [1:0] s, a; wire [1:0] b; m m1(s, a, b); endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top.m1"));
  ASSERT_EQ(kPaths.size(), 1u);
  EXPECT_EQ(TermsOf(vpiModPathIn, kPaths[0]),
            (std::vector<Term>{{"a[0]", vpiNoEdge}}));
  EXPECT_EQ(TermsOf(vpiModPathOut, kPaths[0]),
            (std::vector<Term>{{"b[1]", vpiNoEdge}}));
  vpiHandle condition = vpi_handle(vpiCondition, kPaths[0]);
  EXPECT_EQ(NameOf(condition), "s[1]");
  EXPECT_EQ(NameOf(vpi_handle(vpiParent, condition)), "s");
}

TEST_F(ModulePathsOfARun, AModulePathReportsHowItWasWritten) {
  Run("module m(input clk, input d, input a, input b, output q, "
      "output y, output z);\n"
      "  specify\n"
      "    (a +=> y) = 1;\n"
      "    (b -*> z) = 1;\n"
      "    (posedge clk => (q -: d)) = 1;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg clk, d, a, b; wire q, y, z; "
      "m m1(clk, d, a, b, q, y, z); endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top.m1"));
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(vpi_get(vpiPathType, kPaths[0]), vpiPathParallel);
  EXPECT_EQ(vpi_get(vpiPolarity, kPaths[0]), vpiPositive);
  EXPECT_EQ(vpi_get(vpiPathType, kPaths[1]), vpiPathFull);
  EXPECT_EQ(vpi_get(vpiPolarity, kPaths[1]), vpiNegative);
  EXPECT_EQ(vpi_get(vpiPathType, kPaths[2]), vpiPathParallel);
  EXPECT_EQ(vpi_get(vpiPolarity, kPaths[2]), vpiUnknown);
  EXPECT_EQ(vpi_get(vpiDataPolarity, kPaths[2]), vpiNegative);
}

TEST(ModPathsOfAHandMadeRun, APortlessPathHasNoTermsAndReadsItsHeldDelay) {
  SimFixture f;
  SpecifyPathDecl decl;
  decl.delays = {nullptr};
  PathDelay path;
  path.decl = &decl;
  path.inst_prefix = "u.";
  path.delay_count = 1;
  path.delays[0] = 7;
  path.source_delays = {nullptr};
  f.ctx.AcquireSpecifyManager().MutablePathDelays().push_back(path);
  VpiContext vpi;
  SetGlobalVpiContext(&vpi);
  vpi.Attach(f.ctx);
  vpiHandle paths =
      vpi_iterate(vpiModPath, vpi_handle_by_name(VpiText("u"), nullptr));
  ASSERT_NE(paths, nullptr);
  vpiHandle mod_path = vpi_scan(paths);
  ASSERT_NE(mod_path, nullptr);
  EXPECT_EQ(vpi_iterate(vpiModPathIn, mod_path), nullptr);
  EXPECT_EQ(vpi_iterate(vpiModPathOut, mod_path), nullptr);
  s_vpi_time times[3] = {};
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 1;
  delay.time_type = vpiSimTime;
  delay.mtm_flag = 1;
  vpi_get_delays(mod_path, &delay);
  EXPECT_EQ(times[0].low, 7u);
  EXPECT_EQ(times[1].low, 7u);
  EXPECT_EQ(times[2].low, 7u);
  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
