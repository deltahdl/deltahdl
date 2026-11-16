#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_constraint_item_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SolveBeforeOrdering, RandVariablesAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit s;\n"
             "  rand bit [31:0] d;\n"
             "  constraint c { s -> d == 0; solve s before d; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SolveBeforeOrdering, NonRandVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  rand int y;\n"
             "  constraint c { solve x before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'x' is not a random variable and cannot appear "
                            "in a solve...before ordering constraint",
                            4, "18.5.9"));
}

TEST(SolveBeforeOrdering, RandcVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [3:0] x;\n"
             "  rand int y;\n"
             "  constraint c { solve x before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randc variable 'x' is not allowed in a "
                            "solve...before ordering constraint",
                            4, "18.5.9"));
}

TEST(SolveBeforeOrdering, RandcVariableInAfterListRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int y;\n"
             "  randc bit [3:0] x;\n"
             "  constraint c { solve y before x; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randc variable 'x' is not allowed in a "
                            "solve...before ordering constraint",
                            4, "18.5.9"));
}

TEST(SolveBeforeOrdering, RealVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real r;\n"
             "  rand int y;\n"
             "  constraint c { solve r before y; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SolveBeforeOrdering, ObjectHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class P; endclass\n"
             "class C;\n"
             "  rand P p;\n"
             "  rand int y;\n"
             "  constraint c { solve p before y; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "solve...before ordering variable 'p' shall be of "
                            "integral or real type",
                            5, "18.5.9"));
}

TEST(SolveBeforeOrdering, ArraySizeMethodAcceptedElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  rand int n;\n"
             "  constraint c { solve A.size() before n; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SolveBeforeOrdering, CircularDependencyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a, b;\n"
             "  constraint c { solve a before b; solve b before a; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 3, "18.5.9"));
}

TEST(SolveBeforeOrdering, ThreeNodeCircularDependencyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint k {\n"
             "    solve a before b;\n"
             "    solve b before c;\n"
             "    solve c before a;\n"
             "  }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 4, "18.5.9"));
}

TEST(SolveBeforeOrdering, AcyclicChainAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint k { solve a before b; solve b before c; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(SolveBeforeOrdering, SelfOrderingRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  constraint c { solve a before a; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "circular dependency in solve...before variable ordering", 3, "18.5.9"));
}

const char* const kLeaf =
    "class L; rand bit [3:0] r; bit [3:0] s; randc bit [3:0] rc; endclass";
const char* const kMembers =
    "rand bit [3:0] a, b, c; randc bit [3:0] rc; bit [3:0] s; rand L l; L k; "
    "rand real r; rand int A[4], Q[$], D[]; parameter int P = 1; "
    "localparam int LP = 2; typedef struct { int x; } us_t; rand us_t us; "
    "typedef struct packed { bit [3:0] x; } ps_t; rand ps_t ps; "
    "typedef enum { E0, E1 } e_t; rand e_t e;";
const char* const kScopeDecl =
    "bit [3:0] a, b, c, s; int A[4], Q[$], D[], x; real r;";
const char* const kScopeArgs = "a, b, c, A, Q, D, x, r";
constexpr uint32_t kItemLine = 6;
constexpr ItemPlace kClassPlaces[] = {ItemPlace::kClassBlock,
                                      ItemPlace::kOutOfBlock};
constexpr ItemPlace kObjectPlaces[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline};

std::string OrderingIn(ItemPlace place, const std::string& item) {
  if (place == ItemPlace::kScope)
    return ScopeItemIn(kScopeDecl, kScopeArgs, item);
  return ItemIn(place, kMembers, item, kLeaf);
}

std::string NotRandom(const std::string& name) {
  return "'" + name +
         "' is not a random variable and cannot appear in a solve...before "
         "ordering constraint";
}

std::string RandcOrdered(const std::string& name) {
  return "randc variable '" + name +
         "' is not allowed in a solve...before ordering constraint";
}

std::string NotIntegral(const std::string& name) {
  return "solve...before ordering variable '" + name +
         "' shall be of integral or real type";
}

void ExpectOrderingReport(const std::string& src, const std::string& message,
                          uint32_t line) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "18.5.9"))
      << src;
}

void ExpectOrderingAccepted(const std::string& src) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(src, f)) << src;
}

void ExpectReportedAt(ItemPlace place, const std::string& item,
                      const std::string& message) {
  ExpectOrderingReport(OrderingIn(place, item), message, kItemLine);
}

void ExpectAcceptedAt(ItemPlace place, const std::string& item) {
  ExpectOrderingAccepted(OrderingIn(place, item));
}

TEST(SolveBeforeOrdering,
     AStateMemberIsRejectedInEitherListOfAClassConstraint) {
  for (ItemPlace place : kClassPlaces) {
    ExpectReportedAt(place, "solve s before a;", NotRandom("s"));
    ExpectReportedAt(place, "solve a before s;", NotRandom("s"));
    ExpectAcceptedAt(place, "solve a before b;");
  }
}

TEST(SolveBeforeOrdering, AParameterOrLocalparamIsRejected) {
  for (ItemPlace place : kClassPlaces) {
    ExpectReportedAt(place, "solve P before a;", NotRandom("P"));
    ExpectReportedAt(place, "solve a before LP;", NotRandom("LP"));
  }
}

TEST(SolveBeforeOrdering, DISABLED_AStateMemberIsRejectedInRandomizeWith) {
  ExpectReportedAt(ItemPlace::kInline, "solve s before a;", NotRandom("s"));
  ExpectReportedAt(ItemPlace::kInline, "solve a before s;", NotRandom("s"));
}

TEST(SolveBeforeOrdering, ARandMemberIsAcceptedInRandomizeWith) {
  ExpectAcceptedAt(ItemPlace::kInline, "solve a before b, c;");
}

TEST(SolveBeforeOrdering, DISABLED_ACallersVariableIsRejectedInRandomizeWith) {
  ExpectOrderingReport(
      "class C; rand bit [3:0] a; endclass\n"
      "module t;\n"
      "  bit [3:0] loc;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize() with { solve loc before a; });\n"
      "  end\n"
      "endmodule\n",
      NotRandom("loc"), 6);
}

TEST(SolveBeforeOrdering,
     DISABLED_AVariableNotRandomizedIsRejectedInScopeRandomize) {
  ExpectReportedAt(ItemPlace::kScope, "solve s before a;", NotRandom("s"));
  ExpectReportedAt(ItemPlace::kScope, "solve a before s;", NotRandom("s"));
}

TEST(SolveBeforeOrdering, AnArgumentIsAcceptedInScopeRandomize) {
  ExpectAcceptedAt(ItemPlace::kScope, "solve a before b, c;");
}

TEST(SolveBeforeOrdering, DISABLED_AStateMemberThroughARandHandleIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectReportedAt(place, "solve l.s before a;", NotRandom("l.s"));
  }
}

TEST(SolveBeforeOrdering, ARandMemberThroughARandHandleIsAccepted) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectAcceptedAt(place, "solve l.r before a;");
  }
}

TEST(SolveBeforeOrdering, DISABLED_ARandMemberThroughAStateHandleIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectReportedAt(place, "solve k.r before a;", NotRandom("k.r"));
  }
}

TEST(SolveBeforeOrdering, ARandcVariableIsRejectedOutOfBlock) {
  ExpectReportedAt(ItemPlace::kOutOfBlock, "solve rc before a;",
                   RandcOrdered("rc"));
  ExpectReportedAt(ItemPlace::kOutOfBlock, "solve a before rc;",
                   RandcOrdered("rc"));
  ExpectAcceptedAt(ItemPlace::kOutOfBlock, "solve a before b;");
}

TEST(SolveBeforeOrdering, DISABLED_ARandcVariableIsRejectedInRandomizeWith) {
  ExpectReportedAt(ItemPlace::kInline, "solve rc before a;",
                   RandcOrdered("rc"));
  ExpectReportedAt(ItemPlace::kInline, "solve a before rc;",
                   RandcOrdered("rc"));
}

TEST(SolveBeforeOrdering, DISABLED_ARandcMemberThroughARandHandleIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectReportedAt(place, "solve l.rc before a;", RandcOrdered("l.rc"));
  }
}

TEST(SolveBeforeOrdering, AnEnumOrPackedStructIsAccepted) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectAcceptedAt(place, "solve e before a;");
    ExpectAcceptedAt(place, "solve a before ps;");
  }
}

TEST(SolveBeforeOrdering, DISABLED_AnUnpackedStructIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectReportedAt(place, "solve us before a;", NotIntegral("us"));
  }
}

TEST(SolveBeforeOrdering, DISABLED_AWholeUnpackedArrayIsRejected) {
  for (ItemPlace place : kObjectPlaces) {
    ExpectReportedAt(place, "solve A before a;", NotIntegral("A"));
    ExpectReportedAt(place, "solve a before D;", NotIntegral("D"));
    ExpectReportedAt(place, "solve Q before a;", NotIntegral("Q"));
  }
}

TEST(SolveBeforeOrdering,
     DISABLED_AWholeArrayArgumentIsRejectedInScopeRandomize) {
  ExpectReportedAt(ItemPlace::kScope, "solve A before a;", NotIntegral("A"));
  ExpectReportedAt(ItemPlace::kScope, "solve a before D;", NotIntegral("D"));
  ExpectReportedAt(ItemPlace::kScope, "solve Q before a;", NotIntegral("Q"));
}

TEST(SolveBeforeOrdering, AnElementOrTheSizeOfAnArrayIsAccepted) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectAcceptedAt(place, "solve A[0] before a;");
    ExpectAcceptedAt(place, "solve D.size() before a;");
    ExpectAcceptedAt(place, "solve Q.size() before a;");
    ExpectAcceptedAt(place, "solve a before D.size, Q.size;");
  }
}

TEST(SolveBeforeOrdering, ARealIsAcceptedInEveryPlace) {
  for (ItemPlace place : kEveryItemPlace) {
    ExpectAcceptedAt(place, "solve r before a;");
  }
}

TEST(SolveBeforeOrdering, AHandleIsRejectedOutOfBlock) {
  ExpectReportedAt(ItemPlace::kOutOfBlock, "solve l before a;",
                   NotIntegral("l"));
}

TEST(SolveBeforeOrdering, DISABLED_AHandleIsRejectedInRandomizeWith) {
  ExpectReportedAt(ItemPlace::kInline, "solve l before a;", NotIntegral("l"));
}

const char* const kCycle =
    "circular dependency in solve...before variable ordering";
const char* const kOrderedPair =
    "rand bit [3:0] a, b, c; constraint k0 { solve a before b; }";

TEST(SolveBeforeOrdering, ACycleThroughAListIsRejected) {
  for (ItemPlace place : kClassPlaces) {
    ExpectReportedAt(place, "solve a, b before c; solve c before b;", kCycle);
    ExpectAcceptedAt(place, "solve a, b before c; solve b before c;");
  }
}

TEST(SolveBeforeOrdering, ACycleAcrossTwoClassBlocksIsRejected) {
  for (ItemPlace place : kClassPlaces) {
    ExpectOrderingReport(ItemIn(place, kOrderedPair, "solve b before a;"),
                         kCycle, 2);
    ExpectOrderingAccepted(ItemIn(place, kOrderedPair, "solve b before c;"));
  }
}

TEST(SolveBeforeOrdering,
     DISABLED_ACycleWithAClassBlockInRandomizeWithIsRejected) {
  ExpectOrderingReport(
      ItemIn(ItemPlace::kInline, kOrderedPair, "solve b before a;"), kCycle, 5);
}

TEST(SolveBeforeOrdering, AChainWithAClassBlockInRandomizeWithIsAccepted) {
  ExpectOrderingAccepted(
      ItemIn(ItemPlace::kInline, kOrderedPair, "solve b before c;"));
}

TEST(SolveBeforeOrdering, DISABLED_ACycleWithinAnInlineConstraintIsRejected) {
  for (ItemPlace place : {ItemPlace::kInline, ItemPlace::kScope}) {
    ExpectReportedAt(place, "solve a before b; solve b before a;", kCycle);
    ExpectReportedAt(place, "solve a, b before c; solve c before b;", kCycle);
    ExpectReportedAt(place, "solve a before a;", kCycle);
  }
}

TEST(SolveBeforeOrdering, AChainWithinAnInlineConstraintIsAccepted) {
  for (ItemPlace place : {ItemPlace::kInline, ItemPlace::kScope}) {
    ExpectAcceptedAt(place, "solve a before b; solve b before c;");
  }
}

std::string DerivedOrdering(const std::string& derived_block) {
  return "class B;\n"
         "  rand bit [3:0] a, b, c;\n"
         "  constraint kb { solve a before b; }\n"
         "endclass\n"
         "class D extends B;\n"
         "  constraint " +
         derived_block +
         "\n"
         "endclass\n"
         "module m; endmodule\n";
}

TEST(SolveBeforeOrdering, DISABLED_ACycleAcrossBaseAndDerivedBlocksIsRejected) {
  ExpectOrderingReport(DerivedOrdering("kd { solve b before a; }"), kCycle, 6);
}

TEST(SolveBeforeOrdering, ADerivedBlockContinuingTheBaseChainIsAccepted) {
  ExpectOrderingAccepted(DerivedOrdering("kd { solve b before c; }"));
}

TEST(SolveBeforeOrdering, AnOverridingBlockReplacesTheBaseOrdering) {
  ExpectOrderingAccepted(DerivedOrdering("kb { solve b before a; }"));
}

}  // namespace
