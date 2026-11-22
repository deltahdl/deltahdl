#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForms =
    "module sub; bit x; endmodule\n"
    "module top; int a, b, i, j; bit c; logic [3:0] v;\n"
    "  struct packed { bit f; } s; sub u();\n"
    "  function bit g; return 1; endfunction\n"
    "  task t; endtask\n"
    "  initial if (a) begin : nb b = 1; end\n"
    "  initial if (a) fork b = 1; join\n"
    "  initial if (a) if (b) i = 1;\n"
    "  initial if (a) ;\n"
    "  initial if (a) i = 1; else j = 2;\n"
    "  initial if (c) i++; else j = 1;\n"
    "  initial if (a == 1) i = 1;\n"
    "  initial if (g()) i = 1;\n"
    "  initial if ($time) i = 1;\n"
    "  initial if (1) i = 1;\n"
    "  initial if (v[0]) i = 1;\n"
    "  initial if (v[1:0]) i = 1;\n"
    "  initial if (s.f) i = 1;\n"
    "  initial if (u.x) i = 1;\n"
    "  initial if (a) i = 1; else begin j = 1; end\n"
    "  initial if (a) i = 1; else @(c) j = 1;\n"
    "  initial if (a) i = 1; else case (a) 1: j = 1; endcase\n"
    "  initial if (a) i = 1; else while (0) j = 1;\n"
    "  initial if (a) i = 1; else t();\n"
    "  initial if (a) i = 1; else j <= 1;\n"
    "  initial unique if (a) i = 1;\n"
    "  initial priority if (a) i = 1;\n"
    "  initial unique if (a) i = 1; else if (b) j = 1; else j = 2;\n"
    "  initial unique0 if (a) i = 1; else if (b) j = 1;\n"
    "  initial priority if (a) i = 1; else if (b) j = 1;\n"
    "endmodule\n";

class ConditionalsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle Conditional(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static int KindOf(int relation, size_t n) {
    vpiHandle conditional = Conditional(n);
    vpiHandle reached =
        conditional == nullptr ? nullptr : vpi_handle(relation, conditional);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }

  static vpiHandle ConditionOf(size_t n) {
    vpiHandle conditional = Conditional(n);
    return conditional == nullptr ? nullptr
                                  : vpi_handle(vpiCondition, conditional);
  }

  static void ExpectChainQualifier(size_t n, int nested_type, int qualifier) {
    vpiHandle outer = Conditional(n);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(vpi_get(vpiQualifier, outer), qualifier);
    vpiHandle nested = vpi_handle(vpiElseStmt, outer);
    ASSERT_NE(nested, nullptr);
    EXPECT_EQ(vpi_get(vpiType, nested), nested_type);
    EXPECT_EQ(vpi_get(vpiQualifier, nested), qualifier);
  }
};

TEST_F(ConditionalsEverywhere, ANamedBlockThenBranchIsANamedBegin) {
  EXPECT_EQ(KindOf(vpiStmt, 0), vpiNamedBegin);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiStmt, Conditional(0))), "nb");
}

TEST_F(ConditionalsEverywhere, AForkThenBranchIsAFork) {
  EXPECT_EQ(KindOf(vpiStmt, 1), vpiFork);
}

TEST_F(ConditionalsEverywhere, ANestedIfThenBranchIsAnIf) {
  EXPECT_EQ(KindOf(vpiStmt, 2), vpiIf);
}

TEST_F(ConditionalsEverywhere, AnEmptyThenBranchIsANullStatement) {
  EXPECT_EQ(KindOf(vpiStmt, 3), vpiNullStmt);
}

TEST_F(ConditionalsEverywhere, AnIfElseReachesItsOwnThenBranch) {
  vpiHandle conditional = Conditional(4);
  ASSERT_NE(conditional, nullptr);
  EXPECT_EQ(vpi_get(vpiType, conditional), vpiIfElse);
  EXPECT_EQ(vpi_get(vpiQualifier, conditional), vpiNoQualifier);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, conditional)),
            VpiObjectOf(By("top.a")));
  vpiHandle then = vpi_handle(vpiStmt, conditional);
  ASSERT_NE(then, nullptr);
  EXPECT_EQ(vpi_get(vpiType, then), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, then)), VpiObjectOf(By("top.i")));
}

TEST_F(ConditionalsEverywhere, AnIncrementThenBranchIsItsOwnObject) {
  vpiHandle conditional = Conditional(5);
  ASSERT_NE(conditional, nullptr);
  vpiHandle then = vpi_handle(vpiStmt, conditional);
  ASSERT_NE(then, nullptr);
  EXPECT_NE(VpiObjectOf(then),
            VpiObjectOf(vpi_handle(vpiElseStmt, conditional)));
  EXPECT_EQ(vpi_get(vpiOpType, then), vpiPostIncOp);
}

TEST_F(ConditionalsEverywhere, AnIfConditionCanBeAnOperation) {
  vpiHandle condition = ConditionOf(6);
  EXPECT_EQ(OpOf(condition), vpiEqOp);
  const std::vector<vpiHandle> kSides = OperandsOf(condition);
  ASSERT_EQ(kSides.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kSides[0]), VpiObjectOf(By("top.a")));
  EXPECT_EQ(IntegerOf(kSides[1]), 1);
}

TEST_F(ConditionalsEverywhere, AFunctionCallConditionIsTheCall) {
  vpiHandle condition = ConditionOf(7);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiFuncCall);
  EXPECT_EQ(CalleeOf(condition), "g");
}

TEST_F(ConditionalsEverywhere, ASystemFunctionCallConditionIsTheCall) {
  vpiHandle condition = ConditionOf(8);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiSysFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, condition), "$time");
}

TEST_F(ConditionalsEverywhere, AConstantConditionIsTheConstant) {
  vpiHandle condition = ConditionOf(9);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiConstant);
  EXPECT_EQ(IntegerOf(condition), 1);
}

TEST_F(ConditionalsEverywhere, ABitOfALogicVectorConditionIsAVarBit) {
  vpiHandle condition = ConditionOf(10);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiVarBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, condition)),
            VpiObjectOf(By("top.v")));
}

TEST_F(ConditionalsEverywhere, APartSelectConditionIsAPartSelect) {
  vpiHandle condition = ConditionOf(11);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiPartSelect);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, condition)), 1);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, condition)), 0);
}

TEST_F(ConditionalsEverywhere, AStructMemberConditionIsTheMember) {
  EXPECT_EQ(VpiObjectOf(ConditionOf(12)), VpiObjectOf(By("top.s.f")));
}

TEST_F(ConditionalsEverywhere, AHierarchicalConditionIsWhatItNames) {
  vpiHandle condition = ConditionOf(13);
  ASSERT_NE(condition, nullptr);
  if (vpi_get(vpiType, condition) == vpiRefObj) {
    condition = vpi_handle(vpiActual, condition);
  }
  EXPECT_EQ(VpiObjectOf(condition), VpiObjectOf(By("top.u.x")));
}

TEST_F(ConditionalsEverywhere, AnElseBranchIsReachedByItsOwnKind) {
  EXPECT_EQ(KindOf(vpiElseStmt, 14), vpiBegin);
  EXPECT_EQ(KindOf(vpiElseStmt, 15), vpiEventControl);
  EXPECT_EQ(KindOf(vpiElseStmt, 16), vpiCase);
  EXPECT_EQ(KindOf(vpiElseStmt, 17), vpiWhile);
  EXPECT_EQ(KindOf(vpiElseStmt, 18), vpiTaskCall);
  EXPECT_EQ(KindOf(vpiElseStmt, 19), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiBlocking, vpi_handle(vpiElseStmt, Conditional(19))), 0);
}

TEST_F(ConditionalsEverywhere, AQualifiedPlainIfReportsItsQualifier) {
  ASSERT_NE(Conditional(20), nullptr);
  ASSERT_NE(Conditional(21), nullptr);
  EXPECT_EQ(vpi_get(vpiType, Conditional(20)), vpiIf);
  EXPECT_EQ(vpi_get(vpiQualifier, Conditional(20)), vpiUniqueQualifier);
  EXPECT_EQ(vpi_get(vpiType, Conditional(21)), vpiIf);
  EXPECT_EQ(vpi_get(vpiQualifier, Conditional(21)), vpiPriorityQualifier);
}

TEST_F(ConditionalsEverywhere, DISABLED_AUniqueChainQualifiesItsNestedIfElse) {
  ExpectChainQualifier(22, vpiIfElse, vpiUniqueQualifier);
}

TEST_F(ConditionalsEverywhere, DISABLED_AUnique0ChainQualifiesItsNestedIf) {
  ExpectChainQualifier(23, vpiIf, vpiUniqueQualifier);
}

TEST_F(ConditionalsEverywhere, DISABLED_APriorityChainQualifiesItsNestedIf) {
  ExpectChainQualifier(24, vpiIf, vpiPriorityQualifier);
}

class ConditionalsInEachPlace : public VpiDesignRun {
 protected:
  static vpiHandle BlockUnder(vpiHandle owner) {
    vpiHandle stmt = owner == nullptr ? nullptr : vpi_handle(vpiStmt, owner);
    while (stmt != nullptr) {
      const int kType = vpi_get(vpiType, stmt);
      if (kType == vpiEventControl) {
        stmt = vpi_handle(vpiStmt, stmt);
        continue;
      }
      const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, stmt);
      if (kType != vpiBegin || kInner.size() != 1 ||
          vpi_get(vpiType, kInner[0]) != vpiBegin) {
        break;
      }
      stmt = kInner[0];
    }
    return stmt;
  }

  static vpiHandle ProcessOf(const char* scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By(scope));
    return kProcs.size() == 1 ? kProcs[0] : nullptr;
  }
};

TEST_F(ConditionalsInEachPlace, BothFormsAreTheirOwnKindInEachPlace) {
  Run("package pk; int a, i, j;\n"
      "  task pt; begin if (a) i = 1; if (a) i = 1; else j = 2; end endtask\n"
      "  function void pf; begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "  endfunction\n"
      "endpackage\n"
      "interface ifc; int a, i, j;\n"
      "  initial begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endinterface\n"
      "program prg; int a, i, j;\n"
      "  initial begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endprogram\n"
      "module mal; bit c; int a, i, j;\n"
      "  always @(c) begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endmodule\n"
      "module mac; int a, i, j;\n"
      "  always_comb begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endmodule\n"
      "module maf; bit c; int a, i, j;\n"
      "  always_ff @(posedge c) begin if (a) i <= 1; if (a) i <= 1;\n"
      "    else j <= 2; end\n"
      "endmodule\n"
      "module mat; int a, i, j;\n"
      "  always_latch begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endmodule\n"
      "module mfi; int a, i, j;\n"
      "  final begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "endmodule\n"
      "module mnb; int a, i, j;\n"
      "  initial begin begin if (a) i = 1; if (a) i = 1; else j = 2; end end\n"
      "endmodule\n"
      "module mfk; int a, i, j;\n"
      "  initial fork if (a) i = 1; if (a) i = 1; else j = 2; join\n"
      "endmodule\n"
      "module top; int a, i, j; ifc i0(); prg p0(); mal al(); mac ac();\n"
      "  maf af(); mat at(); mfi fi(); mnb nb(); mfk fk();\n"
      "  class C; int a, i, j;\n"
      "    task ct; begin if (a) i = 1; if (a) i = 1; else j = 2; end endtask\n"
      "  endclass\n"
      "  task tk; begin if (a) i = 1; if (a) i = 1; else j = 2; end endtask\n"
      "  function void fn; begin if (a) i = 1; if (a) i = 1; else j = 2; end\n"
      "  endfunction\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle owner;
  } kPlaces[] = {
      {"pt", Named(vpiTask, By("pk"), "pt")},
      {"pf", Named(vpiFunction, By("pk"), "pf")},
      {"i0", ProcessOf("top.i0")},
      {"p0", ProcessOf("top.p0")},
      {"al", ProcessOf("top.al")},
      {"ac", ProcessOf("top.ac")},
      {"af", ProcessOf("top.af")},
      {"at", ProcessOf("top.at")},
      {"fi", ProcessOf("top.fi")},
      {"nb", ProcessOf("top.nb")},
      {"fk", ProcessOf("top.fk")},
      {"ct", Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct")},
      {"tk", Named(vpiTask, top, "tk")},
      {"fn", Named(vpiFunction, top, "fn")},
  };
  for (const auto& place : kPlaces) {
    vpiHandle block = BlockUnder(place.owner);
    ASSERT_NE(block, nullptr) << place.where;
    EXPECT_EQ(KindsOf(vpiStmt, block), (std::vector<int>{vpiIf, vpiIfElse}))
        << place.where;
  }
}

TEST_F(ConditionalsInEachPlace, AConditionalCanBeARoutinesWholeBody) {
  Run("module top; int a, i, j;\n"
      "  task tk; if (a) i = 1; endtask\n"
      "  function void fn; if (a) i = 1; else j = 2; endfunction\n"
      "endmodule\n");
  vpiHandle task_body = vpi_handle(vpiStmt, Named(vpiTask, By("top"), "tk"));
  vpiHandle function_body =
      vpi_handle(vpiStmt, Named(vpiFunction, By("top"), "fn"));
  ASSERT_NE(task_body, nullptr);
  ASSERT_NE(function_body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, task_body), vpiIf);
  EXPECT_EQ(vpi_get(vpiType, function_body), vpiIfElse);
}

}  // namespace
}  // namespace delta
