#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class MulticlockSequencesEverywhere : public VpiDesignRun {
 protected:
  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static std::string ClockOf(vpiHandle clocked) {
    vpiHandle event = vpi_handle(vpiClockingEvent, clocked);
    if (event == nullptr) return "";
    const char* edge = "";
    if (vpi_get(vpiType, event) == vpiOperation) {
      const int kOp = vpi_get(vpiOpType, event);
      edge = kOp == vpiPosedgeOp ? "+" : kOp == vpiNegedgeOp ? "-" : "?";
      const std::vector<vpiHandle> kOperands = OperandsOf(event);
      return kOperands.size() == 1 ? edge + NameOf(kOperands[0]) : "?";
    }
    return NameOf(event);
  }

  static std::vector<std::string> ClocksOf(vpiHandle multiclock) {
    std::vector<std::string> clocks;
    for (vpiHandle clocked : ObjectsOf(vpiClockedSeq, multiclock)) {
      EXPECT_EQ(vpi_get(vpiType, clocked), vpiClockedSeq);
      clocks.push_back(ClockOf(clocked));
    }
    return clocks;
  }

  static std::vector<vpiHandle> ClockedOf(const char* label) {
    return ObjectsOf(vpiClockedSeq, PropertyOf(label));
  }

  static vpiHandle AssertionBody(const std::string& label) {
    vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
    if (it == nullptr) return nullptr;
    vpiHandle found = nullptr;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      if (found == nullptr && NameOf(h) == label) found = h;
    }
    return vpi_handle(vpiPropertyExpr, vpi_handle(vpiProperty, found));
  }

  static void ExpectTwoClocks(vpiHandle multiclock, const std::string& where) {
    ASSERT_NE(multiclock, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, multiclock), vpiMulticlockSequenceExpr) << where;
    EXPECT_EQ(ClocksOf(multiclock), (std::vector<std::string>{"+c1", "+c2"}))
        << where;
  }
};

constexpr const char* kClockRuns =
    "module top; logic c1, c2, c3, a, b, c;\n"
    "  f1: assert property (@(posedge c1) a ##0 @(posedge c2) b);\n"
    "  t1: assert property (@(posedge c1) a ##1 @(posedge c2) b ##1 "
    "@(posedge c3) c);\n"
    "  t2: assert property (@(posedge c1) a ##1 @(posedge c2) b ##1 "
    "@(posedge c1) c);\n"
    "  e1: assert property (@(posedge c1) a ##1 @(negedge c1) b);\n"
    "endmodule\n";

TEST_F(MulticlockSequencesEverywhere, AFusionOfTwoClocksGivesTwoClockedSeqs) {
  Run(kClockRuns);
  EXPECT_EQ(ClocksOf(PropertyOf("f1")),
            (std::vector<std::string>{"+c1", "+c2"}));
}

TEST_F(MulticlockSequencesEverywhere, EachRunOfAChainIsAClockedSeqInOrder) {
  Run(kClockRuns);
  EXPECT_EQ(ClocksOf(PropertyOf("t1")),
            (std::vector<std::string>{"+c1", "+c2", "+c3"}));
  EXPECT_EQ(ClocksOf(PropertyOf("t2")),
            (std::vector<std::string>{"+c1", "+c2", "+c1"}));
}

TEST_F(MulticlockSequencesEverywhere, TwoEdgesOfOneSignalAreTwoClockedSeqs) {
  Run(kClockRuns);
  EXPECT_EQ(ClocksOf(PropertyOf("e1")),
            (std::vector<std::string>{"+c1", "-c1"}));
}

TEST_F(MulticlockSequencesEverywhere, ABareSignalClockIsTheSignal) {
  Run("module top; logic c1, c2, a, b;\n"
      "  k1: assert property (@(c1) a ##1 @(posedge c2) b);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kClocked = ClockedOf("k1");
  ASSERT_EQ(kClocked.size(), 2u);
  vpiHandle event = vpi_handle(vpiClockingEvent, kClocked[0]);
  ASSERT_NE(event, nullptr);
  EXPECT_NE(vpi_get(vpiType, event), vpiOperation);
  EXPECT_EQ(NameOf(event), "c1");
}

TEST_F(MulticlockSequencesEverywhere, AnIffClockCarriesItsQualifier) {
  Run("module top; logic c1, c2, en, a, b;\n"
      "  k1: assert property (@(posedge c1 iff en) a ##1 @(posedge c2) b);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kClocked = ClockedOf("k1");
  ASSERT_EQ(kClocked.size(), 2u);
  vpiHandle event = vpi_handle(vpiClockingEvent, kClocked[0]);
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(OpOf(event), vpiIffOp);
  const std::vector<vpiHandle> kParts = OperandsOf(event);
  ASSERT_EQ(kParts.size(), 2u);
  EXPECT_EQ(OpOf(kParts[0]), vpiPosedgeOp);
  EXPECT_EQ(NameOf(kParts[1]), "en");
}

constexpr const char* kHeldKinds =
    "module top; logic c1, c2, a, b, c, d;\n"
    "  sequence s; c ##1 d; endsequence\n"
    "  h1: assert property (@(posedge c1) a ##1 @(posedge c2) b);\n"
    "  h2: assert property (@(posedge c1) a ##1 @(posedge c2) s);\n"
    "  h3: assert property (@(posedge c1) a ##1 @(posedge c2) "
    "b dist {0 := 1, 1 := 3});\n"
    "endmodule\n";

TEST_F(MulticlockSequencesEverywhere, ABareBooleanIsHeldAsItsVariable) {
  Run(kHeldKinds);
  const std::vector<vpiHandle> kClocked = ClockedOf("h1");
  ASSERT_EQ(kClocked.size(), 2u);
  EXPECT_EQ(NameOf(vpi_handle(vpiLogicVar, kClocked[1])), "b");
  EXPECT_EQ(vpi_handle(vpiOperation, kClocked[1]), nullptr);
}

TEST_F(MulticlockSequencesEverywhere, ASequenceInstIsHeldAsTheInst) {
  Run(kHeldKinds);
  const std::vector<vpiHandle> kClocked = ClockedOf("h2");
  ASSERT_EQ(kClocked.size(), 2u);
  vpiHandle inst = vpi_handle(vpiSequenceInst, kClocked[1]);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(NameOf(vpi_handle(vpiSequenceDecl, inst)), "s");
}

TEST_F(MulticlockSequencesEverywhere, ADistributionIsHeldAsTheDistribution) {
  Run(kHeldKinds);
  const std::vector<vpiHandle> kClocked = ClockedOf("h3");
  ASSERT_EQ(kClocked.size(), 2u);
  EXPECT_NE(vpi_handle(vpiDistribution, kClocked[1]), nullptr);
}

constexpr const char* kTwoClocks = "@(posedge c1) a ##1 @(posedge c2) b";

std::string Directives(const char* prefix) {
  const std::string kBody = kTwoClocks;
  const std::string kName = prefix;
  return "  " + kName + "a: assert property (" + kBody + ");\n  " + kName +
         "u: assume property (" + kBody + ");\n  " + kName +
         "c: cover property (" + kBody + ");\n  " + kName +
         "s: cover sequence (" + kBody + ");\n";
}

TEST_F(MulticlockSequencesEverywhere, EveryDirectiveHoldsTheMulticlock) {
  Run("module top; logic c1, c2, a, b;\n" + Directives("m") + "endmodule\n");
  for (const char* label : {"ma", "mu", "mc", "ms"}) {
    ExpectTwoClocks(AssertionBody(label), label);
  }
}

TEST_F(MulticlockSequencesEverywhere,
       APropertyDeclarationsBodyIsTheMulticlock) {
  Run(std::string("module top; logic c1, c2, a, b;\n  property p; ") +
      kTwoClocks + "; endproperty\nendmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  ExpectTwoClocks(
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl)), "p");
}

TEST_F(MulticlockSequencesEverywhere, InstancesAssertionsHoldTheMulticlock) {
  Run(std::string("interface ifc; logic c1, c2, a, b;\n") + Directives("i") +
      "endinterface\n"
      "program prg; logic c1, c2, a, b;\n" +
      Directives("r") +
      "endprogram\n"
      "checker chk; logic c1, c2, a, b;\n" +
      Directives("k") +
      "endchecker\n"
      "module top; ifc i0(); prg pr0(); chk k0(); endmodule\n");
  for (const char* label : {"ia", "iu", "ic", "is", "ra", "ru", "rc", "rs",
                            "ka", "ku", "kc", "ks"}) {
    ExpectTwoClocks(AssertionBody(label), label);
  }
}

TEST_F(MulticlockSequencesEverywhere, APackagesSequenceIsTheMulticlock) {
  Run(std::string("package pk; logic c1, c2, a, b;\n  sequence ps; ") +
      kTwoClocks + "; endsequence\nendpackage\nmodule top; endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("pk"), "ps");
  ASSERT_NE(decl, nullptr);
  ExpectTwoClocks(vpi_handle(vpiExpr, decl), "ps");
}

TEST_F(MulticlockSequencesEverywhere,
       DISABLED_ACompilationUnitsSequenceIsTheMulticlock) {
  Run(std::string("logic c1, c2, a, b;\nsequence us; ") + kTwoClocks +
      "; endsequence\nmodule top; endmodule\n");
  vpiHandle decl =
      Named(vpiSequenceDecl, Named(vpiPackage, nullptr, "$unit"), "us");
  ASSERT_NE(decl, nullptr);
  ExpectTwoClocks(vpi_handle(vpiExpr, decl), "us");
}

}  // namespace
}  // namespace delta
