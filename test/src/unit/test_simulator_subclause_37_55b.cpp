#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ImmediateAssertionsEverywhere : public VpiDesignRun {
 protected:
  struct Expected {
    const char* label;
    int type;
    int deferred;
    int final;
    const char* stmt;
    const char* else_stmt;
  };

  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static vpiHandle AssertionNamed(const std::string& label) {
    vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
    if (it == nullptr) return nullptr;
    vpiHandle found = nullptr;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      if (found == nullptr && NameOf(h) == label) found = h;
    }
    return found;
  }

  static void ExpectParts(const Expected& expected) {
    vpiHandle assertion = AssertionNamed(expected.label);
    ASSERT_NE(assertion, nullptr) << expected.label;
    EXPECT_EQ(vpi_get(vpiType, assertion), expected.type) << expected.label;
    EXPECT_EQ(vpi_get(vpiIsDeferred, assertion), expected.deferred)
        << expected.label;
    EXPECT_EQ(vpi_get(vpiIsFinal, assertion), expected.final) << expected.label;
    EXPECT_EQ(NameOf(vpi_handle(vpiExpr, assertion)), "a") << expected.label;
    EXPECT_EQ(ActionReached(vpiStmt, assertion), expected.stmt)
        << expected.label;
    EXPECT_EQ(ActionReached(vpiElseStmt, assertion), expected.else_stmt)
        << expected.label;
  }

  static void ExpectEach(const std::vector<Expected>& all) {
    for (const Expected& expected : all) ExpectParts(expected);
  }

  static void ExpectKinds(const std::string& prefix) {
    const struct {
      const char* suffix;
      int type;
    } kKinds[] = {{"t", vpiImmediateAssert},
                  {"u", vpiImmediateAssume},
                  {"v", vpiImmediateCover}};
    for (const auto& kind : kKinds) {
      const std::string kLabel = prefix + kind.suffix;
      vpiHandle assertion = AssertionNamed(kLabel);
      ASSERT_NE(assertion, nullptr) << kLabel;
      EXPECT_EQ(vpi_get(vpiType, assertion), kind.type) << kLabel;
      EXPECT_EQ(NameOf(vpi_handle(vpiExpr, assertion)), "a") << kLabel;
    }
  }

  static vpiHandle ExprOf(const char* label) {
    return vpi_handle(vpiExpr, AssertionNamed(label));
  }
};

constexpr const char* kDeferredItems =
    "module top; logic a;\n"
    "  m1: assert final (a) $display(\"p\"); else $write(\"f\");\n"
    "  m2: assume #0 (a) $display(\"p\"); else $write(\"f\");\n"
    "  m3: assume final (a) $display(\"p\"); else $write(\"f\");\n"
    "  m4: cover #0 (a) $display(\"p\");\n"
    "  m5: cover final (a) $display(\"p\");\n"
    "  m6: assert #0 (a);\n"
    "  m7: assume final (a);\n"
    "endmodule\n";

TEST_F(ImmediateAssertionsEverywhere, DeferredItemsReachTheirParts) {
  Run(kDeferredItems);
  ExpectEach({{"m1", vpiImmediateAssert, 1, 1, "$display", "$write"},
              {"m2", vpiImmediateAssume, 1, 0, "$display", "$write"},
              {"m3", vpiImmediateAssume, 1, 1, "$display", "$write"},
              {"m4", vpiImmediateCover, 1, 0, "$display", ""},
              {"m5", vpiImmediateCover, 1, 1, "$display", ""},
              {"m6", vpiImmediateAssert, 1, 0, "", ""},
              {"m7", vpiImmediateAssume, 1, 1, "", ""}});
}

constexpr const char* kProceduralForms =
    "module top; logic a;\n"
    "  initial begin\n"
    "    p1: assume (a) $display(\"p\"); else $write(\"f\");\n"
    "    p2: cover (a) $display(\"p\");\n"
    "    p3: assert #0 (a) $display(\"p\"); else $write(\"f\");\n"
    "    p4: assert final (a) $display(\"p\"); else $write(\"f\");\n"
    "    p5: assume #0 (a) $display(\"p\"); else $write(\"f\");\n"
    "    p6: assume final (a) $display(\"p\"); else $write(\"f\");\n"
    "    p7: cover #0 (a) $display(\"p\");\n"
    "    p8: cover final (a) $display(\"p\");\n"
    "  end\n"
    "  always_comb begin\n"
    "    q1: assert final (a) $display(\"p\"); else $write(\"f\");\n"
    "    q2: assert #0 (a) $display(\"p\");\n"
    "  end\n"
    "endmodule\n";

TEST_F(ImmediateAssertionsEverywhere, ASimpleAssumeAndCoverAreNeither) {
  Run(kProceduralForms);
  ExpectEach({{"p1", vpiImmediateAssume, 0, 0, "$display", "$write"},
              {"p2", vpiImmediateCover, 0, 0, "$display", ""}});
}

TEST_F(ImmediateAssertionsEverywhere, ProceduralDeferredFormsReachTheirParts) {
  Run(kProceduralForms);
  ExpectEach({{"p3", vpiImmediateAssert, 1, 0, "$display", "$write"},
              {"p4", vpiImmediateAssert, 1, 1, "$display", "$write"},
              {"p5", vpiImmediateAssume, 1, 0, "$display", "$write"},
              {"p6", vpiImmediateAssume, 1, 1, "$display", "$write"},
              {"p7", vpiImmediateCover, 1, 0, "$display", ""},
              {"p8", vpiImmediateCover, 1, 1, "$display", ""},
              {"q1", vpiImmediateAssert, 1, 1, "$display", "$write"},
              {"q2", vpiImmediateAssert, 1, 0, "$display", ""}});
}

TEST_F(ImmediateAssertionsEverywhere, AnActionlessAssertionReachesNoStmt) {
  Run("module top; logic a;\n"
      "  initial begin\n"
      "    n1: assert (a);\n"
      "    n2: assume (a);\n"
      "    n3: cover (a);\n"
      "  end\n"
      "endmodule\n");
  ExpectEach({{"n1", vpiImmediateAssert, 0, 0, "", ""},
              {"n2", vpiImmediateAssume, 0, 0, "", ""},
              {"n3", vpiImmediateCover, 0, 0, "", ""}});
}

TEST_F(ImmediateAssertionsEverywhere, APassActionIsTheStatementWritten) {
  Run("module top; logic a; int c;\n"
      "  initial begin\n"
      "    s1: assert (a) begin c = 1; end\n"
      "    s2: assume (a) begin : blk c = 2; end\n"
      "    s3: cover (a) c = 3;\n"
      "  end\n"
      "endmodule\n");
  const struct {
    const char* label;
    int type;
  } kActions[] = {
      {"s1", vpiBegin}, {"s2", vpiNamedBegin}, {"s3", vpiAssignment}};
  for (const auto& action : kActions) {
    vpiHandle stmt = vpi_handle(vpiStmt, AssertionNamed(action.label));
    ASSERT_NE(stmt, nullptr) << action.label;
    EXPECT_EQ(vpi_get(vpiType, stmt), action.type) << action.label;
  }
}

constexpr const char* kExprKinds =
    "module top; logic a, b; logic [3:0] v;\n"
    "  function automatic bit f(); return 1; endfunction\n"
    "  initial begin\n"
    "    e1: assert (a && b);\n"
    "    e2: assume (1);\n"
    "    e3: cover (v[2]);\n"
    "    e4: assert (v[2:1]);\n"
    "    e5: assert (f());\n"
    "  end\n"
    "endmodule\n";

TEST_F(ImmediateAssertionsEverywhere, AnOperationIsReachedWithItsOperands) {
  Run(kExprKinds);
  vpiHandle op = ExprOf("e1");
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(OpOf(op), vpiLogAndOp);
  std::vector<std::string> names;
  for (vpiHandle operand : OperandsOf(op)) names.push_back(NameOf(operand));
  EXPECT_EQ(names, (std::vector<std::string>{"a", "b"}));
}

TEST_F(ImmediateAssertionsEverywhere, EachExprIsReachedAsItsOwnKind) {
  Run(kExprKinds);
  const struct {
    const char* label;
    int type;
  } kExprs[] = {{"e2", vpiConstant},
                {"e3", vpiVarBit},
                {"e4", vpiPartSelect},
                {"e5", vpiFuncCall}};
  for (const auto& expr : kExprs) {
    vpiHandle reached = ExprOf(expr.label);
    ASSERT_NE(reached, nullptr) << expr.label;
    EXPECT_EQ(vpi_get(vpiType, reached), expr.type) << expr.label;
  }
}

constexpr const char* kThreeKinds = "(a); ";

std::string ThreeKinds(const std::string& prefix, const char* form) {
  return "    " + prefix + "t: assert " + form + kThreeKinds + prefix +
         "u: assume " + form + kThreeKinds + prefix + "v: cover " + form +
         kThreeKinds + "\n";
}

TEST_F(ImmediateAssertionsEverywhere, ATasksAndAFunctionsAreTheirKinds) {
  Run("module top; logic a;\n"
      "  task automatic tk();\n" +
      ThreeKinds("k", "") +
      "  endtask\n"
      "  function automatic void fn();\n" +
      ThreeKinds("f", "") +
      "  endfunction\n"
      "  initial begin tk(); fn(); end\n"
      "endmodule\n");
  ExpectKinds("k");
  ExpectKinds("f");
}

TEST_F(ImmediateAssertionsEverywhere, AClassMethodsAreTheirKinds) {
  Run("module top; logic a;\n"
      "  class cl;\n"
      "    function void m();\n" +
      ThreeKinds("c", "") +
      "    endfunction\n"
      "  endclass\n"
      "  cl h;\n"
      "  initial begin h = new; h.m(); end\n"
      "endmodule\n");
  ExpectKinds("c");
}

TEST_F(ImmediateAssertionsEverywhere, AProgramsAreTheirKinds) {
  Run("program prg; logic a;\n"
      "  initial begin\n" +
      ThreeKinds("r", "") +
      "  end\n"
      "endprogram\n"
      "module top; prg pr0(); endmodule\n");
  ExpectKinds("r");
}

TEST_F(ImmediateAssertionsEverywhere, AnInterfacesAreTheirKinds) {
  Run("interface ifc; logic a;\n"
      "  initial begin\n" +
      ThreeKinds("i", "") +
      "  end\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n");
  ExpectKinds("i");
}

TEST_F(ImmediateAssertionsEverywhere, ACheckersAreTheirKinds) {
  Run("checker chk; logic a;\n" + ThreeKinds("h", "#0 ") +
      "endchecker\n"
      "module top; chk k0(); endmodule\n");
  ExpectKinds("h");
}

TEST_F(ImmediateAssertionsEverywhere, AGenerateBlocksAreTheirKinds) {
  Run("module top; logic a;\n"
      "  if (1) begin : g\n"
      "    initial begin\n" +
      ThreeKinds("g", "") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  ExpectKinds("g");
}

}  // namespace
}  // namespace delta
