#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ModuleItemsOfARun : public VpiDesignRun {
 protected:
  void RunPreprocessed(const std::string& src) {
    auto fid = f_.mgr.AddFile("<test>", src);
    Preprocessor preproc(f_.mgr, f_.diag, {});
    auto pp = preproc.Preprocess(fid);
    auto pp_fid =
        f_.mgr.AddPreprocessedFile("<preprocessed>", pp, preproc.LineOrigins());
    Lexer lexer(f_.mgr.FileContent(pp_fid), pp_fid, f_.diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, f_.arena, f_.diag);
    CompilationUnit* cu = parser.Parse();
    PropagateDirectivesToCu(cu, preproc);
    Elaborator elab(f_.arena, f_.diag, cu);
    RtlirDesign* design = elab.Elaborate(TopNameOf(cu));
    f_.has_errors.Record(src);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }

  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static std::vector<std::string> SidesOf(int side, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle stmt : ObjectsOf(vpiAliasStmt, ref)) {
      names.push_back(NameOf(vpi_handle(side, stmt)));
    }
    return names;
  }
};

TEST_F(ModuleItemsOfARun, AWrittenDecayTimeDirectiveIsReported) {
  RunPreprocessed(
      "`default_decay_time 100\n"
      "module top; endmodule\n");
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), 100);
}

TEST_F(ModuleItemsOfARun, AnInfiniteDecayTimeDirectiveIsUndefined) {
  RunPreprocessed(
      "`default_decay_time infinite\n"
      "module top; endmodule\n");
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), vpiUndefined);
}

TEST_F(ModuleItemsOfARun, AModuleWritingNoAliasHasNoAliasIterator) {
  Run("module top; wire a, b; endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiAliasStmt, By("top")), nullptr);
}

TEST_F(ModuleItemsOfARun, AnInterfaceInstanceReachesItsAliasStatement) {
  Run("interface ifc; wire a, b; alias a = b; endinterface\n"
      "module top; ifc i (); endmodule\n");
  EXPECT_EQ(SidesOf(vpiLhs, By("top.i")), (std::vector<std::string>{"a"}));
  EXPECT_EQ(SidesOf(vpiRhs, By("top.i")), (std::vector<std::string>{"b"}));
}

TEST_F(ModuleItemsOfARun, TwoAliasStatementsAreReachedInSourceOrder) {
  Run("module top; wire a, b, c, d; alias c = d; alias a = b; endmodule\n");
  EXPECT_EQ(SidesOf(vpiLhs, By("top")), (std::vector<std::string>{"c", "a"}));
  EXPECT_EQ(SidesOf(vpiRhs, By("top")), (std::vector<std::string>{"d", "b"}));
}

TEST_F(ModuleItemsOfARun, AFourOperandChainGivesThreeStatements) {
  Run("module top; wire a, b, c, d; alias a = b = c = d; endmodule\n");
  EXPECT_EQ(SidesOf(vpiLhs, By("top")),
            (std::vector<std::string>{"a", "b", "c"}));
  EXPECT_EQ(SidesOf(vpiRhs, By("top")),
            (std::vector<std::string>{"d", "d", "d"}));
}

TEST_F(ModuleItemsOfARun, ATwoOperandAliasGivesOneStatement) {
  Run("module top; wire a, b; alias a = b; endmodule\n");
  EXPECT_EQ(SidesOf(vpiLhs, By("top")), (std::vector<std::string>{"a"}));
  EXPECT_EQ(SidesOf(vpiRhs, By("top")), (std::vector<std::string>{"b"}));
}

TEST_F(ModuleItemsOfARun, AChainOfSelectsKeepsEachOperandsExpression) {
  Run("module top; wire [7:0] w; wire [1:0] x, y; wire [3:0] z;\n"
      "  alias w[3:0] = {x, y} = z;\n"
      "endmodule\n");
  std::vector<vpiHandle> stmts = ObjectsOf(vpiAliasStmt, By("top"));
  ASSERT_EQ(stmts.size(), 2U);
  vpiHandle part = vpi_handle(vpiLhs, stmts[0]);
  ASSERT_NE(part, nullptr);
  EXPECT_EQ(vpi_get(vpiType, part), vpiPartSelect);
  EXPECT_EQ(NameOf(vpi_handle(vpiParent, part)), "w");
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, part)), 3);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, part)), 0);
  vpiHandle concat = vpi_handle(vpiLhs, stmts[1]);
  ASSERT_NE(concat, nullptr);
  EXPECT_EQ(OpOf(concat), vpiConcatOp);
  std::vector<std::string> operands;
  for (vpiHandle operand : ObjectsOf(vpiOperand, concat)) {
    operands.push_back(NameOf(operand));
  }
  EXPECT_EQ(operands, (std::vector<std::string>{"x", "y"}));
  for (vpiHandle stmt : stmts) {
    vpiHandle rhs = vpi_handle(vpiRhs, stmt);
    ASSERT_NE(rhs, nullptr);
    EXPECT_EQ(vpi_get(vpiType, rhs), vpiNet);
    EXPECT_EQ(NameOf(rhs), "z");
  }
}

TEST_F(ModuleItemsOfARun, ASelectAsTheLastOperandIsEveryRightHandSide) {
  Run("module top; wire [7:0] w; wire [1:0] x, y; wire [3:0] z;\n"
      "  alias z = {x, y} = w[7:4];\n"
      "endmodule\n");
  std::vector<vpiHandle> stmts = ObjectsOf(vpiAliasStmt, By("top"));
  ASSERT_EQ(stmts.size(), 2U);
  for (vpiHandle stmt : stmts) {
    vpiHandle rhs = vpi_handle(vpiRhs, stmt);
    ASSERT_NE(rhs, nullptr);
    EXPECT_EQ(vpi_get(vpiType, rhs), vpiPartSelect);
    EXPECT_EQ(NameOf(vpi_handle(vpiParent, rhs)), "w");
    EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, rhs)), 7);
    EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, rhs)), 4);
  }
}

TEST_F(ModuleItemsOfARun, ADefParamReachesTheModuleHoldingIt) {
  Run("module sub #(parameter W = 1); endmodule\n"
      "module top; sub u (); defparam u.W = 8; endmodule\n");
  std::vector<vpiHandle> defparams = ObjectsOf(vpiDefParam, By("top"));
  ASSERT_EQ(defparams.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, defparams[0])),
            VpiObjectOf(By("top")));
}

TEST_F(ModuleItemsOfARun, ADeepDefParamBelongsToTheModuleWritingIt) {
  Run("module leaf #(parameter W = 1); endmodule\n"
      "module mid; leaf v (); endmodule\n"
      "module top; mid u (); defparam u.v.W = 8; endmodule\n");
  std::vector<vpiHandle> defparams = ObjectsOf(vpiDefParam, By("top"));
  ASSERT_EQ(defparams.size(), 1U);
  EXPECT_EQ(vpi_iterate(vpiDefParam, By("top.u")), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, defparams[0])),
            VpiObjectOf(Named(vpiParameter, By("top.u.v"), "W")));
  vpiHandle rhs = vpi_handle(vpiRhs, defparams[0]);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(IntOf(rhs), 8);
}

TEST_F(ModuleItemsOfARun, APortReachesItsInstance) {
  Run("module sub(input logic d); endmodule\n"
      "module top(input logic a); logic w; sub u (.d(w)); endmodule\n");
  vpiHandle d = Named(vpiPort, By("top.u"), "d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, d)), VpiObjectOf(By("top.u")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, d)), VpiObjectOf(By("top.u")));
  vpiHandle a = Named(vpiPort, By("top"), "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, a)), VpiObjectOf(By("top")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, a)), VpiObjectOf(By("top")));
}

TEST_F(ModuleItemsOfARun, AnInterfaceInstanceIteratesItsPorts) {
  Run("interface ifc(input logic clk, input logic rst); endinterface\n"
      "module top; logic c, r; ifc i (c, r); endmodule\n");
  EXPECT_EQ(NamesOf(vpiPort, By("top.i")),
            (std::vector<std::string>{"clk", "rst"}));
}

TEST_F(ModuleItemsOfARun, AProgramInstanceIteratesItsPorts) {
  Run("program prg(input logic clk, output logic done); endprogram\n"
      "module top; logic c, d; prg p (c, d); endmodule\n");
  EXPECT_EQ(NamesOf(vpiPort, By("top.p")),
            (std::vector<std::string>{"clk", "done"}));
}

TEST_F(ModuleItemsOfARun, AnInterfaceOutsideAnArrayReachesNoArray) {
  Run("interface ifc; endinterface\n"
      "module top; ifc one (); ifc ifs[1:0] (); endmodule\n");
  ASSERT_NE(By("top.one"), nullptr);
  EXPECT_EQ(vpi_handle(vpiInstanceArray, By("top.one")), nullptr);
}

TEST_F(ModuleItemsOfARun, AProgramElementReachesItsArray) {
  Run("program prg; endprogram\n"
      "module top; prg p[1:0] (); endmodule\n");
  vpiHandle element = By("top.p[1]");
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstanceArray, element)),
            VpiObjectOf(By("top.p")));
}

TEST_F(ModuleItemsOfARun, AProgramOutsideAnArrayReachesNoArray) {
  Run("program prg; endprogram\n"
      "module top; prg one (); prg p[1:0] (); endmodule\n");
  ASSERT_NE(By("top.one"), nullptr);
  EXPECT_EQ(vpi_handle(vpiInstanceArray, By("top.one")), nullptr);
}

TEST_F(ModuleItemsOfARun, AnInterfaceArrayIteratesItsElements) {
  Run("interface ifc; endinterface\n"
      "module top; ifc ifs[0:2] (); endmodule\n");
  EXPECT_EQ(KindsOf(vpiInterface, By("top.ifs")),
            (std::vector<int>{vpiInterface, vpiInterface, vpiInterface}));
}

TEST_F(ModuleItemsOfARun, AProgramArrayIteratesItsElements) {
  Run("program prg; endprogram\n"
      "module top; prg p[0:1] (); endmodule\n");
  EXPECT_EQ(KindsOf(vpiProgram, By("top.p")),
            (std::vector<int>{vpiProgram, vpiProgram}));
}

TEST_F(ModuleItemsOfARun, ANestedModuleInheritsTheDefaultDisableIff) {
  Run("module top; logic rst;\n"
      "  default disable iff !rst;\n"
      "  module inner; endmodule\n"
      "  inner u ();\n"
      "endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top.u"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

TEST_F(ModuleItemsOfARun, AnInterfaceReachesItsDefaultDisableIff) {
  Run("interface ifc #(parameter P = 1)(input logic rst);\n"
      "  default disable iff !rst;\n"
      "endinterface\n"
      "module top; logic r; ifc i (r); endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top.i"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

TEST_F(ModuleItemsOfARun, AnInterfaceWithNoDefaultDisableIffReachesNone) {
  Run("interface ifc #(parameter P = 1); endinterface\n"
      "module top; ifc i (); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultDisableIff, By("top.i")), nullptr);
}

TEST_F(ModuleItemsOfARun, ANestedInterfaceInheritsTheDefaultDisableIff) {
  Run("module top; logic rst;\n"
      "  default disable iff !rst;\n"
      "  interface ifc; endinterface\n"
      "  ifc i ();\n"
      "endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top.i"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

TEST_F(ModuleItemsOfARun, AProgramReachesItsDefaultDisableIff) {
  Run("program prg #(parameter P = 1)(input logic rst);\n"
      "  default disable iff !rst;\n"
      "endprogram\n"
      "module top; logic r; prg p (r); endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top.p"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

TEST_F(ModuleItemsOfARun, AProgramWithNoDefaultDisableIffReachesNone) {
  Run("program prg #(parameter P = 1); endprogram\n"
      "module top; prg p (); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultDisableIff, By("top.p")), nullptr);
}

}  // namespace
}  // namespace delta
