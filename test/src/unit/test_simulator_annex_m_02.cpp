#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"

namespace {

TEST(SvVpiUser, PackageAndInterfaceTypes) {
  EXPECT_EQ(vpiPackage, 600);
  EXPECT_EQ(vpiInterface, 601);
  EXPECT_EQ(vpiProgram, 602);
  EXPECT_EQ(vpiModport, 606);
  EXPECT_EQ(vpiTypeParameter, 609);
}

TEST(SvVpiUser, VariableTypes) {
  struct {
    int actual;
    int expected;
  } const kCases[] = {
      {vpiLongIntVar, 610}, {vpiIntVar, 612},   {vpiClassVar, 615},
      {vpiStringVar, 616},  {vpiEnumVar, 617},  {vpiStructVar, 618},
      {vpiBitVar, 620},     {vpiClassObj, 621}, {vpiChandleVar, 622},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(c.actual, c.expected);
  }
}

TEST(SvVpiUser, TypespecTypes) {
  EXPECT_EQ(vpiLongIntTypespec, 625);
  EXPECT_EQ(vpiEnumTypespec, 632);
  EXPECT_EQ(vpiStructTypespec, 633);
  EXPECT_EQ(vpiInterfaceTypespec, 906);
}

TEST(SvVpiUser, OperatorConstants) {
  struct {
    int actual;
    int expected;
  } const kCases[] = {
      {vpiImplyOp, 50},    {vpiPostIncOp, 62},    {vpiWildEqOp, 69},
      {vpiStreamLROp, 71}, {vpiInsideOp, 95},     {vpiNexttimeOp, 89},
      {vpiAlwaysOp, 90},   {vpiEventuallyOp, 91},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(c.actual, c.expected);
  }
}

TEST(SvVpiUser, JoinTypeConstants) {
  EXPECT_EQ(vpiJoin, 0);
  EXPECT_EQ(vpiJoinNone, 1);
  EXPECT_EQ(vpiJoinAny, 2);
}

TEST(SvVpiUser, RandTypeConstants) {
  EXPECT_EQ(vpiNotRand, 1);
  EXPECT_EQ(vpiRand, 2);
  EXPECT_EQ(vpiRandC, 3);
}

TEST(SvVpiUser, DpiAccessTypeConstants) {
  EXPECT_EQ(vpiForkJoinAcc, 1);
  EXPECT_EQ(vpiDPIExportAcc, 3);
  EXPECT_EQ(vpiDPIImportAcc, 4);
}

TEST(SvVpiUserConstants, VariableAndTypespecTypes) {
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_EQ(vpiLogicVar, vpiReg);
  EXPECT_EQ(vpiArrayVar, vpiRegArray);
  EXPECT_EQ(vpiChandleTypespec, 632);
  EXPECT_EQ(vpiEnumConst, 634);
  EXPECT_EQ(vpiIntegerTypespec, 635);
  EXPECT_EQ(vpiTimeTypespec, 636);
  EXPECT_EQ(vpiRealTypespec, 637);
  EXPECT_EQ(vpiArrayTypespec, 642);
  EXPECT_EQ(vpiVoidTypespec, 643);
  EXPECT_EQ(vpiTypespecMember, 644);
  EXPECT_EQ(vpiSequenceTypespec, 696);
  EXPECT_EQ(vpiPropertyTypespec, 697);
  EXPECT_EQ(vpiEventTypespec, 698);
}

TEST(SvVpiUserConstants, StatementMethodAndPatternTypes) {
  EXPECT_EQ(vpiClockingIODecl, 651);
  EXPECT_EQ(vpiDistItem, 645);
  EXPECT_EQ(vpiAliasStmt, 646);
  EXPECT_EQ(vpiThread, 647);
  EXPECT_EQ(vpiMethodFuncCall, 648);
  EXPECT_EQ(vpiMethodTaskCall, 649);
  EXPECT_EQ(vpiClockedProp, 902);
  EXPECT_EQ(vpiReturn, 666);
  EXPECT_EQ(vpiAnyPattern, 667);
  EXPECT_EQ(vpiTaggedPattern, 668);
  EXPECT_EQ(vpiStructPattern, 669);
  EXPECT_EQ(vpiWaitFork, 672);
  EXPECT_EQ(vpiDisableFork, 673);
  EXPECT_EQ(vpiExpectStmt, 674);
  EXPECT_EQ(vpiReturnStmt, 691);
  EXPECT_EQ(vpiFinal, 676);
}

TEST(SvVpiUserConstants, NetAndNettypeTypes) {
  EXPECT_EQ(vpiArrayNet, vpiNetArray);
  EXPECT_EQ(vpiLogicNet, vpiNet);
  EXPECT_EQ(vpiUnionNet, 525);
  EXPECT_EQ(vpiShortRealNet, 526);
  EXPECT_EQ(vpiRealNet, 527);
  EXPECT_EQ(vpiByteNet, 528);
  EXPECT_EQ(vpiShortIntNet, 529);
  EXPECT_EQ(vpiIntNet, 530);
  EXPECT_EQ(vpiLongIntNet, 531);
  EXPECT_EQ(vpiBitNet, 532);
  EXPECT_EQ(vpiInterconnectNet, 533);
  EXPECT_EQ(vpiInterconnectArray, 534);
  EXPECT_EQ(vpiBreak, 684);
  EXPECT_EQ(vpiContinue, 685);
  EXPECT_EQ(vpiNettypeDecl, 523);
}

TEST(SvVpiUserConstants, ConstraintAndLetTypes) {
  EXPECT_EQ(vpiConstraintExpr, 747);
  EXPECT_EQ(vpiElseConst, 748);
  EXPECT_EQ(vpiImplication, 749);
  EXPECT_EQ(vpiConstrIf, 738);
  EXPECT_EQ(vpiConstrIfElse, 739);
  EXPECT_EQ(vpiConstrForEach, 736);
  EXPECT_EQ(vpiSoftDisable, 733);
  EXPECT_EQ(vpiLetDecl, 903);
  EXPECT_EQ(vpiLetExpr, 904);
}

TEST(SvVpiUserConstants, OneToOneRelations) {
  EXPECT_EQ(vpiIndexTypespec, 702);
  EXPECT_EQ(vpiNetTypedefAlias, 705);
  EXPECT_EQ(vpiInputSkew, 706);
  EXPECT_EQ(vpiOutputSkew, 707);
  EXPECT_EQ(vpiGlobalClocking, 708);
  EXPECT_EQ(vpiDefaultClocking, 709);
  EXPECT_EQ(vpiDefaultDisableIff, 710);
  EXPECT_EQ(vpiOrigin, 713);
  EXPECT_EQ(vpiPrefix, 714);
  EXPECT_EQ(vpiWith, 715);
  EXPECT_EQ(vpiValueRange, 720);
  EXPECT_EQ(vpiPattern, 721);
  EXPECT_EQ(vpiWeight, 722);
  EXPECT_EQ(vpiConstraintItem, 746);
}

TEST(SvVpiUserConstants, OneToManyRelations) {
  EXPECT_EQ(vpiInterfaceDecl, vpiVirtualInterfaceVar);
  EXPECT_EQ(vpiSolveBefore, 731);
  EXPECT_EQ(vpiSolveAfter, 732);
  EXPECT_EQ(vpiWaitingProcesses, 734);
  EXPECT_EQ(vpiMessages, 735);
  EXPECT_EQ(vpiLoopVars, 737);
  EXPECT_EQ(vpiConcurrentAssertion, 740);
  EXPECT_EQ(vpiConcurrentAssertions, vpiConcurrentAssertion);
  EXPECT_EQ(vpiMember, 742);
  EXPECT_EQ(vpiElement, 743);
}

TEST(SvVpiUserConstants, GenericObjectProperties) {
  EXPECT_EQ(vpiArrayMember, 607);
  EXPECT_EQ(vpiIsRandomized, 608);
  EXPECT_EQ(vpiLocalVarDecls, 609);
  EXPECT_EQ(vpiPortType, 611);
  EXPECT_EQ(vpiInterfacePort, 1);
  EXPECT_EQ(vpiModportPort, 2);
  EXPECT_EQ(vpiConstantVariable, 612);
  EXPECT_EQ(vpiStructUnionMember, 615);
  EXPECT_EQ(vpiOneStepConst, 9);
  EXPECT_EQ(vpiUnboundedConst, 10);
  EXPECT_EQ(vpiNullConst, 11);
  EXPECT_EQ(vpiDistType, 625);
  EXPECT_EQ(vpiEqualDist, 1);
  EXPECT_EQ(vpiDivDist, 2);
  EXPECT_EQ(vpiPacked, 630);
  EXPECT_EQ(vpiTagged, 632);
  EXPECT_EQ(vpiRef, 6);
  EXPECT_EQ(vpiVirtual, 635);
  EXPECT_EQ(vpiHasActual, 636);
  EXPECT_EQ(vpiIsConstraintEnabled, 638);
  EXPECT_EQ(vpiSoft, 639);
  EXPECT_EQ(vpiMailboxClass, 1);
  EXPECT_EQ(vpiSemaphoreClass, 2);
  EXPECT_EQ(vpiUserDefinedClass, 3);
  EXPECT_EQ(vpiProcessClass, 4);
  EXPECT_EQ(vpiMethod, 645);
  EXPECT_EQ(vpiIsDeferred, 657);
  EXPECT_EQ(vpiIsFinal, 670);
  EXPECT_EQ(vpiQualifier, 650);
  EXPECT_EQ(vpiNoQualifier, 0);
  EXPECT_EQ(vpiUniqueQualifier, 1);
  EXPECT_EQ(vpiPriorityQualifier, 2);
  EXPECT_EQ(vpiTaggedQualifier, 4);
  EXPECT_EQ(vpiRandQualifier, 8);
  EXPECT_EQ(vpiInsideQualifier, 16);
  EXPECT_EQ(vpiInputEdge, 651);
  EXPECT_EQ(vpiOutputEdge, 652);
  EXPECT_EQ(vpiGeneric, 653);
  EXPECT_EQ(vpiCompatibilityMode, 654);
  EXPECT_EQ(vpiMode1364v1995, 1);
  EXPECT_EQ(vpiMode1364v2001, 2);
  EXPECT_EQ(vpiMode1364v2005, 3);
  EXPECT_EQ(vpiMode1800v2005, 4);
}

TEST(SvVpiUserConstants, OperatorAndMiscProperties) {
  EXPECT_EQ(vpiMode1800v2009, 5);
  EXPECT_EQ(vpiPackedArrayMember, 655);
  EXPECT_EQ(vpiObjId, 660);
  EXPECT_EQ(vpiIsModPort, 669);
  EXPECT_EQ(vpiMatchOp, 66);
  EXPECT_EQ(vpiCastOp, 67);
  EXPECT_EQ(vpiMatchedOp, 73);
  EXPECT_EQ(vpiTriggeredOp, 74);
  EXPECT_EQ(vpiAssignmentPatternOp, 75);
  EXPECT_EQ(vpiMultiAssignmentPatternOp, 76);
  EXPECT_EQ(vpiOtherFunc, 6);
  EXPECT_EQ(vpiValidUnknown, 2);
  EXPECT_EQ(vpiCoveredMax, 766);
}

// Edge case: the listing documents vpiQualifier as carrying a bitwise OR of the
// qualifier flags, so each flag (other than the "none" sentinel) must be a
// single distinct bit and the flags must compose without overlapping.
TEST(SvVpiUserConstants, QualifierFlagsComposeAsDistinctBits) {
  EXPECT_EQ(vpiNoQualifier, 0);
  const int kFlags[] = {vpiUniqueQualifier, vpiPriorityQualifier,
                        vpiTaggedQualifier, vpiRandQualifier,
                        vpiInsideQualifier};
  int combined = 0;
  for (int flag : kFlags) {
    // Exactly one bit set (power of two).
    EXPECT_NE(flag, 0);
    EXPECT_EQ(flag & (flag - 1), 0);
    // No bit shared with any flag seen so far.
    EXPECT_EQ(combined & flag, 0);
    combined |= flag;
  }
  // All five flags OR-combine into a five-bit mask.
  EXPECT_EQ(combined, vpiUniqueQualifier | vpiPriorityQualifier |
                          vpiTaggedQualifier | vpiRandQualifier |
                          vpiInsideQualifier);
}

// Edge case: each enumerated property value-set the listing introduces must
// assign a distinct selector to every member so the values are unambiguous.
TEST(SvVpiUserConstants, EnumeratedPropertyValuesAreDistinct) {
  const int kClassKinds[] = {vpiMailboxClass, vpiSemaphoreClass,
                             vpiUserDefinedClass, vpiProcessClass};
  for (size_t i = 0; i < std::size(kClassKinds); ++i) {
    for (size_t j = i + 1; j < std::size(kClassKinds); ++j) {
      EXPECT_NE(kClassKinds[i], kClassKinds[j]);
    }
  }

  const int kCompatModes[] = {vpiMode1364v1995, vpiMode1364v2001,
                              vpiMode1364v2005, vpiMode1800v2005,
                              vpiMode1800v2009};
  for (size_t i = 0; i < std::size(kCompatModes); ++i) {
    for (size_t j = i + 1; j < std::size(kCompatModes); ++j) {
      EXPECT_NE(kCompatModes[i], kCompatModes[j]);
    }
  }

  // vpiConstType return values, distribution kinds, and port-type values.
  EXPECT_NE(vpiOneStepConst, vpiUnboundedConst);
  EXPECT_NE(vpiUnboundedConst, vpiNullConst);
  EXPECT_NE(vpiOneStepConst, vpiNullConst);
  EXPECT_NE(vpiEqualDist, vpiDivDist);
  EXPECT_NE(vpiInterfacePort, vpiModportPort);
}

// Edge case: the deprecated/alias spellings the listing defines must resolve to
// the very same selector as their canonical counterparts, so production code
// using either spelling is interchangeable.
TEST(SvVpiUserConstants, AliasSpellingsResolveToCanonicalSelectors) {
  EXPECT_EQ(vpiConcurrentAssertions, vpiConcurrentAssertion);
  EXPECT_EQ(vpiConcurrentAssertions, 740);
  EXPECT_EQ(vpiInterfaceDecl, vpiVirtualInterfaceVar);
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_EQ(vpiLogicVar, vpiReg);
  EXPECT_EQ(vpiArrayVar, vpiRegArray);
  EXPECT_EQ(vpiArrayNet, vpiNetArray);
  EXPECT_EQ(vpiLogicNet, vpiNet);
}

}  // namespace
