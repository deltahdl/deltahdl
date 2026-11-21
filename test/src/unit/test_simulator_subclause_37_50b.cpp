#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ConcurrentAssertionsEverywhere : public VpiDesignRun {
 protected:
  static vpiHandle AssertionAt(const std::string& full_name) {
    for (vpiHandle obj : ObjectsOf(vpiAssertion, nullptr)) {
      const char* own = vpi_get_str(vpiFullName, obj);
      if (own != nullptr && full_name == own) return obj;
    }
    return nullptr;
  }

  static std::string ClockOf(vpiHandle assertion) {
    return Described(vpi_handle(vpiClockingEvent, assertion));
  }

  static std::string Described(vpiHandle event) {
    if (event == nullptr) return "none";
    if (vpi_get(vpiType, event) != vpiOperation) {
      const char* name = vpi_get_str(vpiName, event);
      return name == nullptr ? "unnamed" : name;
    }
    std::string text;
    switch (vpi_get(vpiOpType, event)) {
      case vpiPosedgeOp:
        text = "posedge";
        break;
      case vpiNegedgeOp:
        text = "negedge";
        break;
      case vpiEventOrOp:
        text = "or";
        break;
      default:
        text = "op";
    }
    for (vpiHandle operand : ObjectsOf(vpiOperand, event)) {
      text += " " + Described(operand);
    }
    return text;
  }

  static int PropertyKindOf(vpiHandle assertion) {
    vpiHandle property = vpi_handle(vpiProperty, assertion);
    return property == nullptr ? 0 : vpi_get(vpiType, property);
  }
};

struct Place {
  const char* name;
  const char* before;
  const char* after;
  const char* scope;
  const char* inferring;
  std::string kinds;
};

constexpr const char* kDefaultClocking =
    "  default clocking cb @(negedge clk); endclocking\n";

struct Directive {
  char label;
  int type;
  int is_cover_sequence;
  const char* pass;
  const char* fail;
  const char* written;
  const char* inferred;
};

constexpr Directive kDirectives[] = {
    {'a', vpiAssert, 0, "$display", "$write",
     "  a1: assert property (@(posedge clk) a) $display(\"p\"); "
     "else $write(\"f\");\n",
     "  a2: assert property (a);\n"},
    {'s', vpiAssume, 0, "$display", "$write",
     "  s1: assume property (@(posedge clk) a) $display(\"p\"); "
     "else $write(\"f\");\n",
     "  s2: assume property (a);\n"},
    {'c', vpiCover, 0, "$display", "",
     "  c1: cover property (@(posedge clk) a) $display(\"p\");\n",
     "  c2: cover property (a);\n"},
    {'q', vpiCover, 1, "$display", "",
     "  q1: cover sequence (@(posedge clk) a) $display(\"p\");\n",
     "  q2: cover sequence (a);\n"},
    {'r', vpiRestrict, 0, "", "",
     "  r1: restrict property (@(posedge clk) a);\n",
     "  r2: restrict property (a);\n"}};

class EveryPlaceOfAnAssertion : public ConcurrentAssertionsEverywhere,
                                public ::testing::WithParamInterface<Place> {
 protected:
  std::vector<Directive> Present() const {
    std::vector<Directive> present;
    for (const Directive& directive : kDirectives) {
      if (GetParam().kinds.find(directive.label) != std::string::npos) {
        present.push_back(directive);
      }
    }
    return present;
  }

  void RunWith(bool inferring) {
    std::string src = std::string(GetParam().before) +
                      (inferring ? GetParam().inferring : "");
    for (const Directive& directive : Present()) {
      src += inferring ? directive.inferred : directive.written;
    }
    Run(src + GetParam().after);
  }

  vpiHandle Of(const Directive& directive, const char* suffix) {
    return AssertionAt(std::string(GetParam().scope) + "." + directive.label +
                       suffix);
  }
};

TEST_P(EveryPlaceOfAnAssertion, AWrittenClockDirectiveReportsItsModel) {
  RunWith(false);
  for (const Directive& directive : Present()) {
    SCOPED_TRACE(std::string(1, directive.label));
    vpiHandle assertion = Of(directive, "1");
    ASSERT_NE(assertion, nullptr);
    EXPECT_EQ(vpi_get(vpiType, assertion), directive.type);
    EXPECT_EQ(vpi_get(vpiIsCoverSequence, assertion),
              directive.is_cover_sequence);
    EXPECT_EQ(vpi_get(vpiIsClockInferred, assertion), 0);
    EXPECT_EQ(ClockOf(assertion), "posedge clk");
    EXPECT_EQ(PropertyKindOf(assertion), vpiPropertySpec);
    EXPECT_EQ(ActionReached(vpiStmt, assertion), directive.pass);
    EXPECT_EQ(ActionReached(vpiElseStmt, assertion), directive.fail);
  }
}

TEST_P(EveryPlaceOfAnAssertion, AnInferredClockDirectiveReportsItsModel) {
  RunWith(true);
  for (const Directive& directive : Present()) {
    SCOPED_TRACE(std::string(1, directive.label));
    vpiHandle assertion = Of(directive, "2");
    ASSERT_NE(assertion, nullptr);
    EXPECT_EQ(vpi_get(vpiType, assertion), directive.type);
    EXPECT_EQ(vpi_get(vpiIsClockInferred, assertion), 1);
    EXPECT_EQ(ClockOf(assertion), "negedge clk");
  }
}

std::string PlaceName(const ::testing::TestParamInfo<Place>& info) {
  return info.param.name;
}

INSTANTIATE_TEST_SUITE_P(
    WrittenIn, EveryPlaceOfAnAssertion,
    ::testing::Values(
        Place{"AModule", "module top; logic clk, a;\n", "endmodule\n", "top",
              kDefaultClocking, "ascqr"},
        Place{"AProcedure",
              "module top; logic clk, a;\n  always @(negedge clk) begin\n",
              "  end\nendmodule\n", "top", "", "ascq"},
        Place{"AGenerateBlock",
              "module top; logic clk, a;\n  if (1) begin : g\n",
              "  end\nendmodule\n", "top.g", kDefaultClocking, "ascqr"},
        Place{"AnInterface", "interface ifc(input logic clk, a);\n",
              "endinterface\n"
              "module top; logic clk, a; ifc i(clk, a); endmodule\n",
              "top.i", kDefaultClocking, "ascqr"},
        Place{"AProgram", "program prg(input logic clk, a);\n",
              "endprogram\n"
              "module top; logic clk, a; prg p(clk, a); endmodule\n",
              "top.p", kDefaultClocking, "ascqr"},
        Place{"AChecker", "checker chk(logic clk, logic a);\n",
              "endchecker\n"
              "module top; logic clk, a; chk k(clk, a); endmodule\n",
              "top.k", kDefaultClocking, "ascqr"}),
    PlaceName);

TEST_F(ConcurrentAssertionsEverywhere,
       DISABLED_AProceduralRestrictIsARestrict) {
  Run("module top; logic clk, a;\n"
      "  always @(negedge clk) begin\n"
      "    r1: restrict property (@(posedge clk) a);\n"
      "    r2: restrict property (a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle r1 = AssertionAt("top.r1");
  vpiHandle r2 = AssertionAt("top.r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(vpi_get(vpiType, r1), vpiRestrict);
  EXPECT_EQ(ClockOf(r1), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r1), 0);
  EXPECT_EQ(PropertyKindOf(r1), vpiPropertySpec);
  EXPECT_EQ(ActionReached(vpiStmt, r1), "");
  EXPECT_EQ(ActionReached(vpiElseStmt, r1), "");
  EXPECT_EQ(vpi_get(vpiType, r2), vpiRestrict);
  EXPECT_EQ(ClockOf(r2), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r2), 1);
}

TEST_F(ConcurrentAssertionsEverywhere,
       ADeclaredPropertyIsAPropertyInstAndSuppliesTheClock) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "  a1: assert property (p);\n"
      "  s1: assume property (p);\n"
      "  c1: cover property (p);\n"
      "  r1: restrict property (p);\n"
      "endmodule\n");
  for (const char* name : {"top.a1", "top.s1", "top.c1", "top.r1"}) {
    SCOPED_TRACE(name);
    vpiHandle assertion = AssertionAt(name);
    ASSERT_NE(assertion, nullptr);
    EXPECT_EQ(PropertyKindOf(assertion), vpiPropertyInst);
    EXPECT_EQ(ClockOf(assertion), "posedge clk");
  }
}

constexpr const char* kClockingBlockClock =
    "module top; logic clk, a;\n"
    "  default clocking dcb @(negedge clk); endclocking\n"
    "  clocking cb @(posedge clk); endclocking\n"
    "  a1: assert property (@(cb) a);\n"
    "endmodule\n";

TEST_F(ConcurrentAssertionsEverywhere, AClockingBlocksNameIsAWrittenClock) {
  Run(kClockingBlockClock);
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 0);
}

TEST_F(ConcurrentAssertionsEverywhere,
       DISABLED_AClockingBlocksNameClocksOnTheBlocksEvent) {
  Run(kClockingBlockClock);
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ClockOf(a1), "posedge clk");
}

TEST_F(ConcurrentAssertionsEverywhere, ABareSignalClockIsTheWholeEvent) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(clk) a);\n"
      "endmodule\n");
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ClockOf(a1), "clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 0);
}

TEST_F(ConcurrentAssertionsEverywhere, AnEventListClockIsTheWholeList) {
  Run("module top; logic x, y, a;\n"
      "  a1: assert property (@(posedge x or posedge y) a);\n"
      "endmodule\n");
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ClockOf(a1), "or posedge x posedge y");
}

TEST_F(ConcurrentAssertionsEverywhere, AMulticlockedAssertionsClockIsItsFirst) {
  Run("module top; logic c1, c2, a, b;\n"
      "  a1: assert property (@(posedge c1) a ##1 @(posedge c2) b);\n"
      "endmodule\n");
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ClockOf(a1), "posedge c1");
}

TEST_F(ConcurrentAssertionsEverywhere, AGlobalClockIsWrittenNotInferred) {
  Run("module top; logic clk, a;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  a1: assert property (@$global_clock a);\n"
      "endmodule\n");
  vpiHandle a1 = AssertionAt("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 0);
}

std::vector<std::string> g_reached;

PLI_INT32 RecordAssertionEvent(PLI_INT32, s_vpi_time*, vpiHandle assertion,
                               p_vpi_attempt_info, PLI_BYTE8*) {
  g_reached.emplace_back(vpi_get_str(vpiName, assertion));
  return 0;
}

PLI_INT32 PlaceOnEveryAssertion(PLI_BYTE8*) {
  vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
  while (vpiHandle assertion = it == nullptr ? nullptr : vpi_scan(it)) {
    for (int reason : {cbAssertionStart, cbAssertionSuccess, cbAssertionFailure,
                       cbAssertionVacuousSuccess}) {
      vpi_register_assertion_cb(assertion, reason, &RecordAssertionEvent,
                                nullptr);
    }
  }
  return 0;
}

class RestrictDuringARun : public ConcurrentAssertionsEverywhere {
 protected:
  void SetUp() override {
    ConcurrentAssertionsEverywhere::SetUp();
    SetGlobalAssertionApi(&api_);
    g_reached.clear();
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    ConcurrentAssertionsEverywhere::TearDown();
  }

  AssertionApi api_;
};

TEST_F(RestrictDuringARun, OnlyTheAssertBesideARestrictReportsEvents) {
  s_vpi_systf_data place = {};
  place.type = vpiSysTask;
  place.tfname = VpiText("$place");
  place.calltf = &PlaceOnEveryAssertion;
  ASSERT_NE(vpi_register_systf(&place), nullptr);
  Run("module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "  r1: restrict property (@(posedge clk) a);\n"
      "  initial begin\n"
      "    $place;\n"
      "    #1 clk = 1; #1 clk = 0; #1 clk = 1; #1 clk = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(g_reached.empty());
  for (const std::string& name : g_reached) EXPECT_EQ(name, "a1");
}

}  // namespace
}  // namespace delta
