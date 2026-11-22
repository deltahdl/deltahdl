#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_assertion_sites.h"
#include "parser/ast_design.h"
#include "preprocessor/preprocessor.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct AssertionKind {
  int type;
  const char* label;
};

constexpr AssertionKind kAssertionKinds[] = {
    {vpiSequenceInst, "sequence instance"},
    {vpiAssert, "assert"},
    {vpiAssume, "assume"},
    {vpiCover, "cover"},
    {vpiRestrict, "restrict"},
    {vpiPropertyInst, "property instance"},
    {vpiImmediateAssert, "immediate assert"},
    {vpiImmediateAssume, "immediate assume"},
    {vpiImmediateCover, "immediate cover"},
};

class AssertionStaticInformationItems : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(AssertionStaticInformationItems, EveryListedAssertionTypeReportsItself) {
  for (const AssertionKind& kind : kAssertionKinds) {
    VpiObject assertion;
    assertion.type = kind.type;

    EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&assertion)), kind.type)
        << kind.label;
    EXPECT_NE(vpi_get(vpiType, VpiHandleOf(&assertion)), vpiAssertion)
        << kind.label;
  }
}

TEST_F(AssertionStaticInformationItems, NameInstanceAndModuleDefinition) {
  VpiObject first_instance;
  first_instance.type = vpiModule;
  first_instance.name = "u1";
  first_instance.def_name = "handshake";
  VpiObject in_first;
  in_first.type = vpiAssert;
  in_first.name = "handshake_p";
  in_first.parent = &first_instance;
  first_instance.children = {&in_first};

  VpiObject second_instance;
  second_instance.type = vpiModule;
  second_instance.name = "u2";
  second_instance.def_name = "handshake";
  VpiObject in_second;
  in_second.type = vpiAssert;
  in_second.name = "handshake_p";
  in_second.parent = &second_instance;
  second_instance.children = {&in_second};

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&in_first)), "handshake_p");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&in_first))),
            &first_instance);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&in_second))),
            &second_instance);
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle(vpiInstance, VpiHandleOf(&in_first))),
      "handshake");
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle(vpiInstance, VpiHandleOf(&in_second))),
      "handshake");
}

TEST_F(AssertionStaticInformationItems, SourceInformationIsFileLineAndColumn) {
  VpiObject first;
  first.type = vpiAssert;
  first.file = "handshake.sv";
  first.start_line = 12;
  first.column = 5;
  first.end_line = 12;
  first.end_column = 30;

  VpiObject second;
  second.type = vpiCover;
  second.file = "handshake.sv";
  second.start_line = 12;
  second.column = 40;

  EXPECT_STREQ(vpi_get_str(vpiFile, VpiHandleOf(&first)), "handshake.sv");
  EXPECT_EQ(vpi_get(vpiStartLine, VpiHandleOf(&first)), 12);
  EXPECT_EQ(vpi_get(vpiColumn, VpiHandleOf(&first)), 5);
  EXPECT_EQ(vpi_get(vpiEndLine, VpiHandleOf(&first)), 12);
  EXPECT_EQ(vpi_get(vpiEndColumn, VpiHandleOf(&first)), 30);

  EXPECT_EQ(vpi_get(vpiStartLine, VpiHandleOf(&second)),
            vpi_get(vpiStartLine, VpiHandleOf(&first)));
  EXPECT_NE(vpi_get(vpiColumn, VpiHandleOf(&second)),
            vpi_get(vpiColumn, VpiHandleOf(&first)));
}

TEST_F(AssertionStaticInformationItems, TheClockingBlockGoverningTheAssertion) {
  VpiObject clocking;
  clocking.type = vpiClockingBlock;
  clocking.name = "cb";
  VpiObject clocked;
  clocked.type = vpiAssert;
  clocked.children = {&clocking};

  VpiObject unclocked;
  unclocked.type = vpiAssert;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingBlock, VpiHandleOf(&clocked))),
            &clocking);
  EXPECT_EQ(vpi_handle(vpiClockingBlock, VpiHandleOf(&unclocked)), nullptr);
}

TEST_F(AssertionStaticInformationItems, TheClockingExpressionOfTheAssertion) {
  VpiObject event;
  event.type = vpiEventControl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  spec.children = {&event};

  VpiObject inner_event;
  inner_event.type = vpiEventControl;
  VpiObject clocked_property;
  clocked_property.type = vpiClockedProp;
  clocked_property.children = {&inner_event};

  VpiObject unclocked_spec;
  unclocked_spec.type = vpiPropertySpec;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&spec))),
            &event);
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&clocked_property))),
      &inner_event);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, VpiHandleOf(&unclocked_spec)),
            nullptr);
}

class AssertionStaticInformationOfARun : public VpiDesignRun {
 protected:
  void RunPreprocessed(const std::string& src) {
    const uint32_t kFile = f_.mgr.AddFile("<test>", src);
    Preprocessor preproc(f_.mgr, f_.diag, {});
    CompilationUnit* cu = PreprocessAndParseCu(f_, kFile, preproc);
    Elaborator elab(f_.arena, f_.diag, cu);
    RtlirDesign* design = elab.Elaborate(TopNameOf(cu));
    f_.has_errors.Record(src);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }

  static vpiHandle At(const std::string& scope, const char* name) {
    return Named(vpiAssertion, By(scope), name);
  }

  static std::string InstanceOf(const std::string& scope, const char* name) {
    vpiHandle assertion = At(scope, name);
    return AssertionSiteFullName(
        assertion == nullptr ? nullptr : vpi_handle(vpiInstance, assertion));
  }

  static std::string DefNameOf(const std::string& scope, const char* name) {
    vpiHandle assertion = At(scope, name);
    vpiHandle instance =
        assertion == nullptr ? nullptr : vpi_handle(vpiInstance, assertion);
    const char* def =
        instance == nullptr ? nullptr : vpi_get_str(vpiDefName, instance);
    return def == nullptr ? "" : def;
  }

  static std::string BlockOf(const std::string& scope, const char* name) {
    vpiHandle assertion = At(scope, name);
    if (assertion == nullptr) return "no assertion";
    vpiHandle block = vpi_handle(vpiClockingBlock, assertion);
    return block == nullptr ? "" : vpi_get_str(vpiName, block);
  }

  static std::string EventText(vpiHandle event) {
    if (event == nullptr) return "";
    if (vpi_get(vpiType, event) != vpiOperation) {
      const char* name = vpi_get_str(vpiName, event);
      return name == nullptr ? "?" : name;
    }
    std::vector<std::string> operands;
    for (vpiHandle operand : ObjectsOf(vpiOperand, event)) {
      operands.push_back(EventText(operand));
    }
    const int kOp = vpi_get(vpiOpType, event);
    if (kOp == vpiPosedgeOp && operands.size() == 1) {
      return "posedge " + operands[0];
    }
    if (kOp == vpiNegedgeOp && operands.size() == 1) {
      return "negedge " + operands[0];
    }
    if (kOp == vpiEventOrOp && operands.size() == 2) {
      return operands[0] + " or " + operands[1];
    }
    return "op " + std::to_string(kOp);
  }

  static std::string ClockOf(const std::string& scope, const char* name) {
    vpiHandle assertion = At(scope, name);
    if (assertion == nullptr) return "no assertion";
    return EventText(vpi_handle(vpiClockingEvent, assertion));
  }
};

TEST_F(AssertionStaticInformationOfARun, EachAssertionReportsItsFullName) {
  Run(kAssertionSites);
  for (const auto& [scope, name] :
       {std::pair<std::string, std::string>{"top", "pc"},
        {"top", "ad"},
        {"top", "d0"},
        {"top", "df"},
        {"top.b", "ai"},
        {"top.p", "ap"}}) {
    vpiHandle assertion = At(scope, name.c_str());
    ASSERT_NE(assertion, nullptr) << name;
    EXPECT_STREQ(vpi_get_str(vpiName, assertion), name.c_str());
    std::string full_name = scope;
    full_name += ".";
    full_name += name;
    EXPECT_EQ(AssertionSiteFullName(assertion), full_name);
  }
}

TEST_F(AssertionStaticInformationOfARun, ACheckersAssertionReportsItsFullName) {
  Run(kAssertionSites);
  vpiHandle ac = By("top.k.ac");
  ASSERT_NE(ac, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ac), vpiAssert);
  EXPECT_STREQ(vpi_get_str(vpiName, ac), "ac");
  EXPECT_EQ(AssertionSiteFullName(ac), "top.k.ac");
}

TEST_F(AssertionStaticInformationOfARun, EachAssertionReachesItsOwnInstance) {
  Run(kAssertionSites);
  EXPECT_EQ(InstanceOf("top", "pc"), "top");
  EXPECT_EQ(InstanceOf("top", "df"), "top");
  EXPECT_EQ(InstanceOf("top.u1", "as"), "top.u1");
  EXPECT_EQ(InstanceOf("top.u2", "as"), "top.u2");
  EXPECT_EQ(InstanceOf("top.u1.sg", "sg1"), "top.u1");
}

TEST_F(AssertionStaticInformationOfARun, EachAssertionReachesItsModuleName) {
  Run(kAssertionSites);
  EXPECT_EQ(DefNameOf("top.u1", "as"), "sub");
  EXPECT_EQ(DefNameOf("top.u2", "as"), "sub");
  EXPECT_EQ(DefNameOf("top.u1.sg", "sg1"), "sub");
  EXPECT_EQ(DefNameOf("top", "am"), "top");
}

TEST_F(AssertionStaticInformationOfARun,
       AnImmediateFormReachesNoClockingBlock) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  initial begin\n"
      "    i1: assert (a);\n"
      "    i2: assert #0 (a);\n"
      "    i3: assert final (a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BlockOf("top", "i1"), "");
  EXPECT_EQ(BlockOf("top", "i2"), "");
  EXPECT_EQ(BlockOf("top", "i3"), "");
}

constexpr const char* kOwnDefaultClockings =
    "interface bus(input logic clk); logic a;\n"
    "  default clocking bc @(negedge clk); endclocking\n"
    "  ai: assert property (a);\n"
    "endinterface\n"
    "program prg(input logic clk); logic a;\n"
    "  default clocking pcb @(negedge clk); endclocking\n"
    "  ap: assert property (a);\n"
    "endprogram\n"
    "module sub(input logic clk); logic a;\n"
    "  default clocking sc @(negedge clk); endclocking\n"
    "  as: assert property (a);\n"
    "endmodule\n"
    "module top; logic clk;\n"
    "  default clocking tc @(posedge clk); endclocking\n"
    "  bus b(clk); prg p(clk); sub u(clk);\n"
    "endmodule\n";

TEST_F(AssertionStaticInformationOfARun, EachInstanceGivesItsOwnClockingBlock) {
  Run(kOwnDefaultClockings);
  EXPECT_EQ(BlockOf("top.b", "ai"), "bc");
  EXPECT_EQ(BlockOf("top.p", "ap"), "pcb");
  EXPECT_EQ(BlockOf("top.u", "as"), "sc");
}

TEST_F(AssertionStaticInformationOfARun, EachInstanceGivesItsOwnClock) {
  Run(kOwnDefaultClockings);
  EXPECT_EQ(ClockOf("top.b", "ai"), "negedge clk");
  EXPECT_EQ(ClockOf("top.p", "ap"), "negedge clk");
  EXPECT_EQ(ClockOf("top.u", "as"), "negedge clk");
}

TEST_F(AssertionStaticInformationOfARun,
       ANamedPropertyGivesTheClockItDeclares) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "  a1: assert property (p);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top", "a1"), "posedge clk");
}

TEST_F(AssertionStaticInformationOfARun,
       DISABLED_AClockingBlockNameGivesItsEvent) {
  Run("module top; logic clk, a;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  a1: assert property (@(cb) a);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top", "a1"), "posedge clk");
}

TEST_F(AssertionStaticInformationOfARun, ABareSignalAndAnEventListAreTheClock) {
  Run("module top; logic clk, a, b;\n"
      "  a1: assert property (@(clk) a);\n"
      "  a2: assert property (@(posedge a or posedge b) a);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top", "a1"), "clk");
  EXPECT_EQ(ClockOf("top", "a2"), "posedge a or posedge b");
}

TEST_F(AssertionStaticInformationOfARun,
       AMulticlockedPropertyGivesItsLeadClock) {
  Run("module top; logic c1, c2, a, b;\n"
      "  a1: assert property (@(posedge c1) a ##1 @(posedge c2) b);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top", "a1"), "posedge c1");
}

TEST_F(AssertionStaticInformationOfARun, AssumeAndCoverGiveTheirClocks) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  m1: assume property (@(posedge clk) a);\n"
      "  m2: assume property (a);\n"
      "  c1: cover property (@(posedge clk) a);\n"
      "  c2: cover property (a);\n"
      "  s1: cover sequence (@(posedge clk) a);\n"
      "  s2: cover sequence (a);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top", "m1"), "posedge clk");
  EXPECT_EQ(ClockOf("top", "m2"), "negedge clk");
  EXPECT_EQ(ClockOf("top", "c1"), "posedge clk");
  EXPECT_EQ(ClockOf("top", "c2"), "negedge clk");
  EXPECT_EQ(ClockOf("top", "s1"), "posedge clk");
  EXPECT_EQ(ClockOf("top", "s2"), "negedge clk");
}

TEST_F(AssertionStaticInformationOfARun,
       GeneratedAndCheckerAssertionsGetClocks) {
  Run("checker chk(logic c, logic a);\n"
      "  ac: assert property (@(posedge c) a);\n"
      "endchecker\n"
      "module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    ag: assert property (a);\n"
      "  end\n"
      "  chk k(clk, a);\n"
      "endmodule\n");
  EXPECT_EQ(ClockOf("top.g[0]", "ag"), "negedge clk");
  EXPECT_EQ(ClockOf("top.k", "ac").rfind("posedge ", 0), 0u);
}

TEST_F(AssertionStaticInformationOfARun, ALineDirectiveSetsTheFileAndLine) {
  RunPreprocessed(
      "module top; logic clk, a;\n"
      "`line 40 \"checks.sv\" 0\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endmodule\n");
  vpiHandle a1 = At("top", "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFile, a1), "checks.sv");
  EXPECT_EQ(vpi_get(vpiStartLine, a1), 40);
}

constexpr const char* kRestrictAndInsts =
    "module top; logic clk, a;\n"
    "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
    "  property p; @(posedge clk) a; endproperty\n"
    "  r1: restrict property (@(posedge clk) a);\n"
    "  c1: cover sequence (s);\n"
    "  a1: assert property (p);\n"
    "endmodule\n";

TEST_F(AssertionStaticInformationOfARun, ARestrictGivesItsSource) {
  Run(kRestrictAndInsts);
  vpiHandle r1 = At("top", "r1");
  ASSERT_NE(r1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFile, r1), "<test>");
  EXPECT_EQ(vpi_get(vpiStartLine, r1), 4);
  const int kColumn = vpi_get(vpiColumn, r1);
  EXPECT_TRUE(kColumn == 3 || kColumn == 7) << kColumn;
}

vpiHandle FirstOfKind(int type) {
  vpiHandle it =
      vpi_iterate(vpiAssertion, vpi_handle_by_name(VpiText("top"), nullptr));
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpi_get(vpiType, obj) == type) return obj;
  }
  return nullptr;
}

TEST_F(AssertionStaticInformationOfARun,
       DISABLED_ASequenceAndAPropertyInstGiveTheirSource) {
  Run(kRestrictAndInsts);
  for (const auto& [type, line] :
       {std::pair{vpiSequenceInst, 5}, std::pair{vpiPropertyInst, 6}}) {
    vpiHandle inst = FirstOfKind(type);
    ASSERT_NE(inst, nullptr) << type;
    const char* file = vpi_get_str(vpiFile, inst);
    EXPECT_STREQ(file == nullptr ? "" : file, "<test>");
    EXPECT_EQ(vpi_get(vpiStartLine, inst), line);
  }
}

}  // namespace
}  // namespace delta
