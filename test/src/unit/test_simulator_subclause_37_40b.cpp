#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TimingCheckRulesOfARun : public VpiDesignRun {
 protected:
  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) == 1;
  }

  static vpiHandle Check(int kind, const char* inst) {
    for (vpiHandle tchk : ObjectsOf(vpiTchk, By(inst))) {
      if (vpi_get(vpiTchkType, tchk) == kind) return tchk;
    }
    return nullptr;
  }

  static std::string TermOf(int relation, vpiHandle tchk) {
    vpiHandle term = tchk == nullptr ? nullptr : vpi_handle(relation, tchk);
    return term == nullptr ? "<none>" : NameOf(vpi_handle(vpiExpr, term));
  }

  static std::vector<std::string> Arguments(vpiHandle tchk) {
    std::vector<std::string> shown;
    for (vpiHandle arg : ObjectsOf(vpiExpr, tchk)) {
      const int kType = vpi_get(vpiType, arg);
      if (kType == vpiTchkTerm) {
        shown.push_back("term " + NameOf(vpi_handle(vpiExpr, arg)));
      } else if (kType == vpiConstant) {
        shown.push_back(std::to_string(IntegerOf(arg)));
      } else {
        shown.push_back(NameOf(arg));
      }
    }
    return shown;
  }

  static std::vector<int> Limits(vpiHandle tchk, int count) {
    std::vector<s_vpi_time> times(2);
    s_vpi_delay request = {};
    request.da = times.data();
    request.no_of_delays = count;
    request.time_type = vpiSimTime;
    vpi_get_delays(tchk, &request);
    std::vector<int> limits;
    limits.reserve(count);
    for (int i = 0; i < count; ++i) {
      limits.push_back(static_cast<int>(times[i].low));
    }
    return limits;
  }
};

constexpr const char* kRefFirst =
    "module m(input r, input d);\n"
    "  specify\n"
    "    $setuphold(posedge r, d, 1, 1);\n"
    "    $recovery(posedge r, d, 1);\n"
    "    $removal(posedge r, d, 1);\n"
    "    $recrem(posedge r, d, 1, 1);\n"
    "    $skew(posedge r, d, 1);\n"
    "    $timeskew(posedge r, d, 1);\n"
    "    $fullskew(posedge r, d, 1, 1);\n"
    "    $nochange(posedge r, d, 0, 0);\n"
    "    $period(posedge r, 4);\n"
    "  endspecify\n"
    "endmodule\n"
    "module top; reg r, d; m m1(r, d); endmodule\n";

std::vector<int> KindsWithBothEvents() {
  return {vpiSetupHold, vpiRecovery, vpiRemoval,  vpiRecrem,
          vpiSkew,      vpiTimeskew, vpiFullskew, vpiNoChange};
}

TEST_F(TimingCheckRulesOfARun, EveryKindsTermsAreItsReferenceAndDataEvents) {
  Run(kRefFirst);
  for (const int kKind : KindsWithBothEvents()) {
    vpiHandle tchk = Check(kKind, "top.m1");
    ASSERT_NE(tchk, nullptr) << kKind;
    EXPECT_EQ(TermOf(vpiTchkRefTerm, tchk), "r") << kKind;
    EXPECT_EQ(TermOf(vpiTchkDataTerm, tchk), "d") << kKind;
  }
  vpiHandle period = Check(vpiPeriod, "top.m1");
  EXPECT_EQ(TermOf(vpiTchkRefTerm, period), "r");
  EXPECT_EQ(TermOf(vpiTchkDataTerm, period), "<none>");
}

TEST_F(TimingCheckRulesOfARun, EachTermReachesTheCheckItBelongsTo) {
  Run(kRefFirst);
  const std::vector<vpiHandle> kChecks = ObjectsOf(vpiTchk, By("top.m1"));
  ASSERT_EQ(kChecks.size(), 9u);
  for (vpiHandle tchk : kChecks) {
    const int kKind = vpi_get(vpiTchkType, tchk);
    for (const int kRelation : {vpiTchkRefTerm, vpiTchkDataTerm}) {
      vpiHandle term = vpi_handle(kRelation, tchk);
      if (term == nullptr) continue;
      EXPECT_TRUE(Same(vpi_handle(vpiTchk, term), tchk)) << kKind;
    }
  }
}

TEST_F(TimingCheckRulesOfARun, APosedgeEventReportsThePosedgeTransitions) {
  Run(kRefFirst);
  vpiHandle term = vpi_handle(vpiTchkRefTerm, Check(vpiRecovery, "top.m1"));
  ASSERT_NE(term, nullptr);
  EXPECT_EQ(vpi_get(vpiEdge, term), vpiPosedge);
}

constexpr const char* kTopAndLeaf =
    "module leaf(input c);\n"
    "  specify $width(posedge c, 1); endspecify\n"
    "endmodule\n"
    "module bare(input c); endmodule\n"
    "module paths(input c, output e);\n"
    "  assign e = c;\n"
    "  specify (c => e) = 1; endspecify\n"
    "endmodule\n"
    "module top(input a);\n"
    "  wire e;\n"
    "  leaf u(a);\n"
    "  bare b(a);\n"
    "  paths p(a, e);\n"
    "  specify $width(negedge a, 2); endspecify\n"
    "endmodule\n";

TEST_F(TimingCheckRulesOfARun, ACheckReachesTheModuleThatDeclaresIt) {
  Run(kTopAndLeaf);
  for (const char* inst : {"top", "top.u"}) {
    const std::vector<vpiHandle> kChecks = ObjectsOf(vpiTchk, By(inst));
    ASSERT_EQ(kChecks.size(), 1u) << inst;
    EXPECT_TRUE(Same(vpi_handle(vpiModule, kChecks[0]), By(inst))) << inst;
  }
}

TEST_F(TimingCheckRulesOfARun, AModuleDeclaringNoCheckIteratesNone) {
  Run(kTopAndLeaf);
  EXPECT_NE(vpi_iterate(vpiTchk, By("top.u")), nullptr);
  EXPECT_EQ(vpi_iterate(vpiTchk, By("top.b")), nullptr);
  EXPECT_EQ(vpi_iterate(vpiTchk, By("top.p")), nullptr);
}

constexpr const char* kNotifiers =
    "module m(input r, input d);\n"
    "  reg nw, np, nn, nt, nf, nr, nh, nc, nm, ns;\n"
    "  logic nl; bit nb;\n"
    "  specify\n"
    "    $width(posedge r, 2, 1, nw);\n"
    "    $period(posedge r, 4, np);\n"
    "    $nochange(posedge r, d, 5, 6, nn);\n"
    "    $timeskew(posedge r, d, 3, nt, 1, 0);\n"
    "    $fullskew(posedge r, d, 3, 4, nf, 0, 1);\n"
    "    $recrem(posedge r, d, 1, 2, nr, d, r, r, d);\n"
    "    $hold(posedge r, d, 7, nh);\n"
    "    $recovery(posedge r, d, 8, nc);\n"
    "    $removal(posedge r, d, 9, nm);\n"
    "    $skew(posedge r, d, 10, ns);\n"
    "    $setup(d, posedge r, 11, nl);\n"
    "    $setuphold(posedge r, d, 12, 13, nb);\n"
    "  endspecify\n"
    "endmodule\n"
    "module top; reg r, d; m m1(r, d); endmodule\n";

TEST_F(TimingCheckRulesOfARun, ANotifierAtEveryKindsPositionIsReached) {
  Run(kNotifiers);
  struct Expected {
    int kind;
    const char* notifier;
  };
  for (const Expected& want :
       {Expected{vpiWidth, "nw"}, Expected{vpiPeriod, "np"},
        Expected{vpiNoChange, "nn"}, Expected{vpiTimeskew, "nt"},
        Expected{vpiFullskew, "nf"}, Expected{vpiRecrem, "nr"},
        Expected{vpiHold, "nh"}, Expected{vpiRecovery, "nc"},
        Expected{vpiRemoval, "nm"}, Expected{vpiSkew, "ns"}}) {
    vpiHandle tchk = Check(want.kind, "top.m1");
    ASSERT_NE(tchk, nullptr) << want.notifier;
    EXPECT_EQ(NameOf(vpi_handle(vpiTchkNotifier, tchk)), want.notifier);
  }
}

TEST_F(TimingCheckRulesOfARun, ANotifierOfAnotherVariableKindIsReached) {
  Run(kNotifiers);
  for (const char* name : {"nl", "nb"}) {
    vpiHandle tchk = Check(name[1] == 'l' ? vpiSetup : vpiSetupHold, "top.m1");
    ASSERT_NE(tchk, nullptr) << name;
    EXPECT_TRUE(Same(vpi_handle(vpiTchkNotifier, tchk),
                     By(std::string("top.m1.") + name)))
        << name;
  }
}

TEST_F(TimingCheckRulesOfARun,
       AControlledReferenceChecksArgumentsAreAsWritten) {
  Run(kNotifiers);
  EXPECT_EQ(Arguments(Check(vpiWidth, "top.m1")),
            (std::vector<std::string>{"term r", "2", "1", "nw"}));
  EXPECT_EQ(Arguments(Check(vpiPeriod, "top.m1")),
            (std::vector<std::string>{"term r", "4", "np"}));
}

TEST_F(TimingCheckRulesOfARun, EveryOtherKindsArgumentsAreAsWritten) {
  Run(kNotifiers);
  using Args = std::vector<std::string>;
  struct Expected {
    int kind;
    Args args;
  };
  const std::vector<Expected> kWanted = {
      {vpiRecrem, {"term r", "term d", "1", "2", "nr", "d", "r", "r", "d"}},
      {vpiTimeskew, {"term r", "term d", "3", "nt", "1", "0"}},
      {vpiFullskew, {"term r", "term d", "3", "4", "nf", "0", "1"}},
      {vpiNoChange, {"term r", "term d", "5", "6", "nn"}},
      {vpiHold, {"term r", "term d", "7", "nh"}},
      {vpiRecovery, {"term r", "term d", "8", "nc"}},
      {vpiRemoval, {"term r", "term d", "9", "nm"}},
      {vpiSkew, {"term r", "term d", "10", "ns"}}};
  for (const Expected& want : kWanted) {
    EXPECT_EQ(Arguments(Check(want.kind, "top.m1")), want.args) << want.kind;
  }
}

TEST_F(TimingCheckRulesOfARun, ANamedOrComputedLimitKeepsItsOwnType) {
  Run("module m(input r, input d);\n"
      "  specify\n"
      "    specparam tSU = 3;\n"
      "    $setup(d, posedge r, tSU);\n"
      "    $hold(posedge r, d, tSU + 1);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg r, d; m m1(r, d); endmodule\n");
  const std::vector<vpiHandle> kSetup =
      ObjectsOf(vpiExpr, Check(vpiSetup, "top.m1"));
  ASSERT_EQ(kSetup.size(), 3u);
  EXPECT_EQ(vpi_get(vpiType, kSetup[2]), vpiSpecParam);
  EXPECT_EQ(NameOf(kSetup[2]), "tSU");
  const std::vector<vpiHandle> kHold =
      ObjectsOf(vpiExpr, Check(vpiHold, "top.m1"));
  ASSERT_EQ(kHold.size(), 3u);
  EXPECT_EQ(OpOf(kHold[2]), vpiAddOp);
}

TEST_F(TimingCheckRulesOfARun, EveryOtherKindsLimitsAreReadAsWritten) {
  Run("module m(input r, input d);\n"
      "  specify\n"
      "    $recrem(posedge r, d, 3, 4);\n"
      "    $fullskew(posedge r, d, 5, 6);\n"
      "    $hold(posedge r, d, 7);\n"
      "    $recovery(posedge r, d, 8);\n"
      "    $removal(posedge r, d, 9);\n"
      "    $skew(posedge r, d, 10);\n"
      "    $timeskew(posedge r, d, 11);\n"
      "    $period(posedge r, 12);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg r, d; m m1(r, d); endmodule\n");
  EXPECT_EQ(Limits(Check(vpiRecrem, "top.m1"), 2), (std::vector<int>{3, 4}));
  EXPECT_EQ(Limits(Check(vpiFullskew, "top.m1"), 2), (std::vector<int>{5, 6}));
  struct Expected {
    int kind;
    int limit;
  };
  for (const Expected& want :
       {Expected{vpiHold, 7}, Expected{vpiRecovery, 8}, Expected{vpiRemoval, 9},
        Expected{vpiSkew, 10}, Expected{vpiTimeskew, 11},
        Expected{vpiPeriod, 12}}) {
    EXPECT_EQ(Limits(Check(want.kind, "top.m1"), 1),
              (std::vector<int>{want.limit}))
        << want.kind;
  }
}

PLI_INT32 PutSetupTwoHoldFive(PLI_BYTE8*) {
  vpiHandle it =
      vpi_iterate(vpiTchk, vpi_handle_by_name(VpiText("top"), nullptr));
  vpiHandle tchk = it == nullptr ? nullptr : vpi_scan(it);
  if (tchk == nullptr) return 0;
  std::vector<s_vpi_time> limits(2);
  limits[0].type = vpiSimTime;
  limits[0].low = 2;
  limits[1].type = vpiSimTime;
  limits[1].low = 5;
  s_vpi_delay put = {};
  put.da = limits.data();
  put.no_of_delays = 2;
  put.time_type = vpiSimTime;
  vpi_put_delays(tchk, &put);
  return 0;
}

TEST_F(TimingCheckRulesOfARun, BothPutLimitsOfASetupholdAreJudged) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$put_limits");
  task.calltf = &PutSetupTwoHoldFive;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  Run("module top(output logic d, output logic clk);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  reg notifier = 0; int a = 0, b = 0, c = 0;\n"
      "  specify $setuphold(posedge clk, d, 8, 8, notifier); endspecify\n"
      "  always @(notifier)\n"
      "    if ($time < 40) a++; else if ($time < 70) b++; else c++;\n"
      "  initial begin\n"
      "    d = 0; clk = 0;\n"
      "    #1 $put_limits;\n"
      "    #15 d = 1; #4 clk = 1; #10 clk = 0;\n"
      "    #10 clk = 1; #3 d = 0; #7 clk = 0;\n"
      "    #20 clk = 1; #6 d = 1; #4 clk = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(IntegerOf(By("top.a")), 0);
  EXPECT_EQ(IntegerOf(By("top.b")), 1);
  EXPECT_EQ(IntegerOf(By("top.c")), 0);
}

TEST_F(TimingCheckRulesOfARun, ADataEventsConditionIsReached) {
  Run("module m(input r, input d, input en);\n"
      "  specify $setup(d &&& en, posedge r, 1); endspecify\n"
      "endmodule\n"
      "module top; reg r, d, en; m m1(r, d, en); endmodule\n");
  vpiHandle setup = Check(vpiSetup, "top.m1");
  ASSERT_NE(setup, nullptr);
  vpiHandle data = vpi_handle(vpiTchkDataTerm, setup);
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(NameOf(vpi_handle(vpiExpr, data)), "d");
  EXPECT_EQ(NameOf(vpi_handle(vpiCondition, data)), "en");
  EXPECT_EQ(vpi_handle(vpiCondition, vpi_handle(vpiTchkRefTerm, setup)),
            nullptr);
}

TEST_F(TimingCheckRulesOfARun, EveryConditionFormIsAnOperation) {
  Run("module m(input r, input en, input d1, d2, d3, d4, d5);\n"
      "  specify\n"
      "    $hold(posedge r &&& ~en, d1, 1);\n"
      "    $hold(posedge r &&& en == 1'b1, d2, 1);\n"
      "    $hold(posedge r &&& en === 1'b0, d3, 1);\n"
      "    $hold(posedge r &&& en != 1'b1, d4, 1);\n"
      "    $hold(posedge r &&& en !== 1'b0, d5, 1);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg r, en, d1, d2, d3, d4, d5;\n"
      "  m m1(r, en, d1, d2, d3, d4, d5);\n"
      "endmodule\n");
  struct Expected {
    const char* data;
    int op;
    std::size_t operands;
  };
  const std::vector<vpiHandle> kChecks = ObjectsOf(vpiTchk, By("top.m1"));
  ASSERT_EQ(kChecks.size(), 5u);
  for (const Expected& want :
       {Expected{"d1", vpiBitNegOp, 1}, Expected{"d2", vpiEqOp, 2},
        Expected{"d3", vpiCaseEqOp, 2}, Expected{"d4", vpiNeqOp, 2},
        Expected{"d5", vpiCaseNeqOp, 2}}) {
    vpiHandle condition = nullptr;
    for (vpiHandle tchk : kChecks) {
      if (TermOf(vpiTchkDataTerm, tchk) != want.data) continue;
      condition = vpi_handle(vpiCondition, vpi_handle(vpiTchkRefTerm, tchk));
    }
    EXPECT_EQ(OpOf(condition), want.op) << want.data;
    const std::vector<vpiHandle> kOperands = OperandsOf(condition);
    ASSERT_EQ(kOperands.size(), want.operands) << want.data;
    EXPECT_EQ(NameOf(kOperands[0]), "en") << want.data;
  }
}

}  // namespace
}  // namespace delta
