#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class LetsEverywhere : public VpiDesignRun {
 protected:
  static std::string Spelling(vpiHandle obj) {
    if (obj == nullptr) return "null";
    const int kType = vpi_get(vpiType, obj);
    if (kType == vpiConstant) return std::to_string(IntegerOf(obj));
    if (kType == vpiOperation) return "op";
    if (kType == vpiLetExpr) return "let";
    const char* name = vpi_get_str(vpiName, obj);
    return name == nullptr ? "?" : name;
  }

  static std::vector<std::string> Spelled(int relation, vpiHandle ref) {
    std::vector<std::string> spelled;
    for (vpiHandle obj : ObjectsOf(relation, ref)) {
      spelled.push_back(Spelling(obj));
    }
    return spelled;
  }

  static std::vector<vpiHandle> AssignedRhs(vpiHandle scope) {
    std::vector<vpiHandle> sides;
    for (vpiHandle assign : ObjectsOf(vpiContAssign, scope)) {
      sides.push_back(vpi_handle(vpiRhs, assign));
    }
    return sides;
  }

  static vpiHandle LetOf(vpiHandle scope, const char* name) {
    return Named(vpiLetDecl, scope, name);
  }

  static vpiHandle AssertionBody(const std::string& label) {
    vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
    if (it == nullptr) return nullptr;
    vpiHandle found = nullptr;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      if (found == nullptr && Spelling(h) == label) found = h;
    }
    return vpi_handle(vpiPropertyExpr, vpi_handle(vpiProperty, found));
  }

  static vpiHandle FirstAssignedRhs(vpiHandle stmt) {
    if (stmt == nullptr) return nullptr;
    if (vpi_get(vpiType, stmt) == vpiAssignment) {
      return vpi_handle(vpiRhs, stmt);
    }
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      vpiHandle found = FirstAssignedRhs(inner);
      if (found != nullptr) return found;
    }
    return FirstAssignedRhs(vpi_handle(vpiStmt, stmt));
  }

  static int AddendOf(vpiHandle let_expr) {
    vpiHandle body = vpi_handle(vpiExpr, vpi_handle(vpiLetDecl, let_expr));
    const std::vector<vpiHandle> kOperands = OperandsOf(body);
    if (OpOf(body) != vpiAddOp || kOperands.size() != 2) return -1;
    return IntegerOf(kOperands[1]);
  }

  static void ExpectUseOf(vpiHandle used, vpiHandle decl,
                          const std::string& where) {
    ASSERT_NE(used, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, used), vpiLetExpr) << where;
    ASSERT_NE(decl, nullptr) << where;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLetDecl, used)), VpiObjectOf(decl))
        << where;
  }
};

constexpr const char* kFormalLists =
    "module top; logic [3:0] a, b, c, w1, w2, w3, w4, w5, w6, w7;\n"
    "  let f(y, x) = y - x;\n"
    "  let one = 1;\n"
    "  let pick(x = 2, y) = x + y;\n"
    "  let tail(x, y = 3) = x + y;\n"
    "  let typed(int x = 2) = x;\n"
    "  let three(x, y, z) = x + y + z;\n"
    "  assign w1 = tail(a);\n"
    "  assign w2 = pick(.y(b));\n"
    "  assign w3 = pick(.y(b), .x(a));\n"
    "  assign w4 = typed();\n"
    "  assign w5 = three(a, .z(c), .y(b));\n"
    "  assign w6 = f(pick(a, b), c);\n"
    "  assign w7 = one;\n"
    "endmodule\n";

TEST_F(LetsEverywhere, FormalsIterateInDeclarationOrder) {
  Run(kFormalLists);
  EXPECT_EQ(Spelled(vpiSeqFormalDecl, LetOf(By("top"), "f")),
            (std::vector<std::string>{"y", "x"}));
}

TEST_F(LetsEverywhere, ALetWithoutFormalsIteratesNone) {
  Run(kFormalLists);
  vpiHandle one = LetOf(By("top"), "one");
  ASSERT_NE(one, nullptr);
  EXPECT_TRUE(ObjectsOf(vpiSeqFormalDecl, one).empty());
}

TEST_F(LetsEverywhere, ATrailingOmittedArgumentIsItsDefault) {
  Run(kFormalLists);
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 7u);
  EXPECT_EQ(Spelled(vpiArgument, kSides[0]),
            (std::vector<std::string>{"a", "3"}));
}

TEST_F(LetsEverywhere, DISABLED_AFormalLeftOutByNameIsItsDefault) {
  Run(kFormalLists);
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 7u);
  EXPECT_EQ(Spelled(vpiArgument, kSides[1]),
            (std::vector<std::string>{"2", "b"}));
}

TEST_F(LetsEverywhere, DISABLED_NamedActualsComeBackInFormalOrder) {
  Run(kFormalLists);
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 7u);
  EXPECT_EQ(Spelled(vpiArgument, kSides[2]),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(LetsEverywhere, DISABLED_MixedActualsComeBackInFormalOrder) {
  Run(kFormalLists);
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 7u);
  EXPECT_EQ(Spelled(vpiArgument, kSides[4]),
            (std::vector<std::string>{"a", "b", "c"}));
}

TEST_F(LetsEverywhere, ATypedFormalsDefaultIsItsValue) {
  Run(kFormalLists);
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 7u);
  const std::vector<vpiHandle> kArgs = ObjectsOf(vpiArgument, kSides[3]);
  ASSERT_EQ(kArgs.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kArgs[0]), vpiConstant);
  EXPECT_EQ(IntegerOf(kArgs[0]), 2);
}

TEST_F(LetsEverywhere, ALetCallActualIsALetExpr) {
  Run(kFormalLists);
  vpiHandle top = By("top");
  const std::vector<vpiHandle> kSides = AssignedRhs(top);
  ASSERT_EQ(kSides.size(), 7u);
  const std::vector<vpiHandle> kArgs = ObjectsOf(vpiArgument, kSides[5]);
  ASSERT_EQ(kArgs.size(), 2u);
  ExpectUseOf(kArgs[0], LetOf(top, "pick"), "inner");
  EXPECT_EQ(Spelled(vpiArgument, kArgs[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(Spelling(kArgs[1]), "c");
}

TEST_F(LetsEverywhere, DISABLED_ALetsBodyIsItsOnlyExpr) {
  Run(kFormalLists);
  vpiHandle pick = LetOf(By("top"), "pick");
  ASSERT_NE(pick, nullptr);
  const std::vector<vpiHandle> kBodies = ObjectsOf(vpiExpr, pick);
  ASSERT_EQ(kBodies.size(), 1u);
  EXPECT_EQ(OpOf(kBodies[0]), vpiAddOp);
}

TEST_F(LetsEverywhere, DISABLED_AFormallessLetsBodyIsReachedBothWays) {
  Run(kFormalLists);
  vpiHandle one = LetOf(By("top"), "one");
  ASSERT_NE(one, nullptr);
  EXPECT_EQ(Spelling(vpi_handle(vpiExpr, one)), "1");
  EXPECT_EQ(Spelled(vpiExpr, one), (std::vector<std::string>{"1"}));
}

TEST_F(LetsEverywhere, InstancesUseTheirOwnLets) {
  Run("interface ifc; logic [3:0] a, o;\n"
      "  let f(x) = x + 2; assign o = f(a);\n"
      "endinterface\n"
      "program prg; logic [3:0] a, o;\n"
      "  let f(x) = x + 3; assign o = f(a);\n"
      "endprogram\n"
      "checker chk(logic clk); logic a;\n"
      "  let f(x) = x + 4;\n"
      "  ck: assert property (@(posedge clk) f(a));\n"
      "endchecker\n"
      "module top; logic clk; ifc i0(); prg pr0(); chk k0(clk); endmodule\n");
  for (const char* scope : {"top.i0", "top.pr0"}) {
    const std::vector<vpiHandle> kSides = AssignedRhs(By(scope));
    ASSERT_EQ(kSides.size(), 1u) << scope;
    ExpectUseOf(kSides[0], LetOf(By(scope), "f"), scope);
  }
  ExpectUseOf(AssertionBody("ck"), LetOf(By("top.k0"), "f"), "top.k0");
}

TEST_F(LetsEverywhere, DISABLED_ALocalLetIsTheOneItsBlockDeclares) {
  Run("module top; logic [3:0] a; int r1, r2, r3, r4;\n"
      "  let f(x) = x + 1;\n"
      "  initial begin : nb let f(x) = x + 2; r1 = f(a); end\n"
      "  initial fork : fk let f(x) = x + 3; r2 = f(a); join\n"
      "  task automatic t; let f(x) = x + 4; r3 = f(a); endtask\n"
      "  function automatic int g(); let f(x) = x + 5; r4 = f(a); return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, top);
  ASSERT_EQ(kProcs.size(), 2u);
  const struct {
    const char* where;
    vpiHandle stmt;
    int addend;
  } kUses[] = {
      {"begin", vpi_handle(vpiStmt, kProcs[0]), 2},
      {"fork", vpi_handle(vpiStmt, kProcs[1]), 3},
      {"task", vpi_handle(vpiStmt, Named(vpiTask, top, "t")), 4},
      {"function", vpi_handle(vpiStmt, Named(vpiFunction, top, "g")), 5}};
  for (const auto& use : kUses) {
    vpiHandle used = FirstAssignedRhs(use.stmt);
    ASSERT_NE(used, nullptr) << use.where;
    EXPECT_EQ(vpi_get(vpiType, used), vpiLetExpr) << use.where;
    EXPECT_EQ(AddendOf(used), use.addend) << use.where;
  }
}

TEST_F(LetsEverywhere, AnAssertionsLetUseIsALetExpr) {
  Run("module top; logic clk, a, b;\n"
      "  let f(x) = x;\n"
      "  k1: assert property (@(posedge clk) f(a));\n"
      "  k2: assert property (@(posedge clk) a ##1 f(b));\n"
      "  sequence s; a ##1 f(b); endsequence\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle f = LetOf(top, "f");
  ExpectUseOf(PropertyOf("k1"), f, "k1");
  const std::vector<vpiHandle> kDelayed = OperandsOf(PropertyOf("k2"));
  ASSERT_GE(kDelayed.size(), 2u);
  ExpectUseOf(kDelayed[1], f, "k2");
  const std::vector<vpiHandle> kBody =
      OperandsOf(vpi_handle(vpiExpr, Named(vpiSequenceDecl, top, "s")));
  ASSERT_GE(kBody.size(), 2u);
  ExpectUseOf(kBody[1], f, "s");
}

TEST_F(LetsEverywhere, DISABLED_AConstantExpressionsLetUseIsALetExpr) {
  Run("module top;\n"
      "  let w(x) = x * 2;\n"
      "  localparam int P = w(4);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle param = Named(vpiParameter, top, "P");
  ASSERT_NE(param, nullptr);
  ExpectUseOf(vpi_handle(vpiExpr, param), LetOf(top, "w"), "P");
}

}  // namespace
}  // namespace delta
